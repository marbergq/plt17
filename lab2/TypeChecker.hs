module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Env = (Sig,[Context])
type Sig = Map Id ([Type],Type)
type Context = Map Id Type

typecheck :: Program -> Err ()
typecheck (PDefs defs) =
    case addDefs starterSig defs of
        Bad err -> fail err
        Ok sigs  -> case Map.lookup (Id "main") sigs of
          Just ([], Type_int) -> checkDefs (sigs, [Map.empty]) defs
          Just ([], t) -> fail ("main function is not of type int. "
                                ++ "The type is: " ++ show t)
          Just (_, Type_int) -> fail "main function must have zero agruments."
          Just _ -> fail ("main function is not of type int " ++
                          "and has arguments (no arguments are allowed).")
          Nothing -> fail $ "main function not found."

-- This function initializes the signature symbol table
addDefs :: Sig -> [Def] -> Err Sig
addDefs sigs []                         = return sigs
addDefs sigs ( (DFun t f args _):funs ) =
    case Map.lookup f sigs of 
      Nothing -> addDefs (Map.insert f ((reverse (enlistTypes [] args)), t) sigs) funs
      _       -> fail ("function " ++ printTree f ++ " already declared.")

enlistTypes :: [Type] -> [Arg] -> [Type]
enlistTypes list []               = list
enlistTypes list ((ADecl t _):args) = enlistTypes (t:list) args

checkDefs :: Env -> [Def] -> Err ()
checkDefs env [] = return ()
checkDefs env (def:defs) = case checkDef env def of
                              Bad err -> fail err
                              Ok _ -> checkDefs env defs

checkDef :: Env -> Def -> Err ()
checkDef env (DFun t f args stms) = case addArgs (addScope env) args of
  Bad err -> fail ("In function " ++ (show f) ++ ": " ++ err)
  Ok env' -> do checkStms env' stms f
                return ()

addArgs :: Env -> [Arg] -> Err Env
addArgs env [] = Ok env
addArgs env ((ADecl t id):args)
  | t == Type_void = fail "Argument type must not be void."
  | otherwise = case addVar env [id] t of
      Bad err -> fail ("Variable declared twice in argument list. " ++ err)
      Ok env' -> addArgs env' args

--Statements
checkStm :: Env -> Stm -> Id -> Err Env
checkStm env s fid = 
    case s of
        SExp e          -> do inferExp env e
                              return env
        SDecls t ids    -> case t of
                              Type_void -> fail ("Declaration type is void: "
                                                 ++ printTree t)
                              _ -> addVar env ids t
        SInit t id e    -> case t of
                              Type_void -> fail ("Initialization type is void: "
                                                 ++ printTree t)
                              _ -> do checkExp env e t
                                      addVar env [id] t
        SReturn e       -> do t <- lookupFun env fid
                              checkExp env e (snd t)
                              return env
        SWhile e stm    -> do checkExp env e Type_bool
                              checkStm env stm fid
        SBlock stms     -> do checkStms (addScope env) stms fid
                              return env
        SIfElse e s1 s2 -> do checkExp env e Type_bool
                              checkStm env s1 fid
                              checkStm env s2 fid

checkStms :: Env -> [Stm] -> Id -> Err Env
checkStms env [] _ = return env
checkStms env (stm:stms) fid = do env' <- checkStm env stm fid
                                  checkStms env' stms fid

-- Expressions 
-- Johan NTS: I would like to try to use printTree e in the case block
inferExp :: Env -> Exp -> Err Type
inferExp env e =
    case e of
      EInt _         -> return Type_int
      EDouble _      -> return Type_double
      ETrue          -> return Type_bool
      EFalse         -> return Type_bool
      EId x          -> lookupVar env x
      EApp f es      -> do funType <- lookupFun env f
                           case checkArgs env es (fst funType) of
                             Bad err -> fail ("Illegal function call "
                                              ++ printTree f ++ ". " ++ err)
                             Ok _    -> return (snd funType)

      EPlus e1 e2    -> inferBinary [Type_int, Type_double] env e1 e2
      EMinus e1 e2   -> inferBinary [Type_int, Type_double] env e1 e2
      ETimes e1 e2   -> inferBinary [Type_int, Type_double] env e1 e2
      EDiv e1 e2     -> inferBinary [Type_int, Type_double] env e1 e2
      EAss id e      -> do t <- lookupVar env id
                           checkExp env e t
                           return t
      EOr e1 e2      -> inferBinary [Type_bool] env e1 e2
      EAnd e1 e2     -> inferBinary [Type_bool] env e1 e2
      EEq e1 e2      -> inferBinary [Type_int, Type_double, Type_bool] env e1 e2
                        >> return Type_bool
      ENEq e1 e2     -> inferBinary [Type_int, Type_double, Type_bool] env e1 e2
                        >> return Type_bool
      ELt e1 e2      -> inferBinary [Type_int, Type_double] env e1 e2
                        >> return Type_bool
      EGt e1 e2      -> inferBinary [Type_int, Type_double] env e1 e2
                        >> return Type_bool
      ELtEq e1 e2    -> inferBinary [Type_int, Type_double] env e1 e2
                        >> return Type_bool
      EGtEq e1 e2    -> inferBinary [Type_int, Type_double] env e1 e2
                        >> return Type_bool
      EPostIncr x    -> do t <- lookupVar env x
                           if elem t [Type_int, Type_double]
                            then return t
                            else fail "Wrong type in increment expression."
                            -- Try printTree e sometime here
      EPostDecr x    -> do t <- lookupVar env x
                           if elem t [Type_int, Type_double]
                            then return t
                            else fail "Wrong type in decrement expression."
      EPreIncr x     -> do t <- lookupVar env x
                           if elem t [Type_int, Type_double]
                            then return t
                            else fail "Wrong type in increment expression."
      EPreDecr x     -> do t <- lookupVar env x
                           if elem t [Type_int, Type_double]
                            then return t
                            else fail "Wrong type in decrement expression."

inferBinary :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBinary validTypes env e1 e2 = do
    t1 <- inferExp env e1
    if elem t1 validTypes
        then
            case checkExp env e2 t1 of
                Bad err -> fail (printTree e1 ++ " has type " ++ printTree t1
                                 ++ " whereas " ++ err)
                Ok _    -> return t1
        else
            fail $ "Wrong type of expression " ++ printTree t1

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = 
    do t' <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return ()

-- This function is used to check EApp argument list
checkArgs :: Env -> [Exp] -> [Type] -> Err ()
checkArgs env [] [] = return ()
checkArgs env [] _ = fail $ "In argument list: Too few arguments provided."
checkArgs env _ [] = fail $ "In argument list: Too many arguments provided."
checkArgs env (e:es) (t:ts) = case checkExp env e t of
                                Bad err -> fail $ "In argument list: " ++ err
                                Ok _    -> checkArgs env es ts

starterEnv :: Env
starterEnv = (starterSig, [])

--returns a list of signatures including built in funs
starterSig :: Sig
starterSig = Map.insert (Id "printInt") ([Type_int],Type_void) $
             Map.insert (Id "printDouble") ([Type_bool],Type_void) $
             Map.insert (Id "readInt") ([],Type_int) $
             Map.insert (Id "readDouble") ([], Type_bool) 
             (Map.empty)

addVar :: Env -> [Id] -> Type -> Err Env
addVar env [] _ = return env
addVar (sig, scope:rest) (x:xs) t = 
    case Map.lookup x scope of
      Nothing -> addVar (sig, ((Map.insert x t scope):rest)) xs t
      Just _  -> fail ("Variable " ++ printTree x ++ " already declared.")

lookupVar :: Env -> Id -> Err Type
lookupVar (_, []) x = fail $ "Unknown variable " ++ printTree x ++ "."
lookupVar (sigs, (scope:rest)) x = case Map.lookup x scope of
                             Nothing -> lookupVar (sigs, rest) x
                             Just t  -> return t

lookupFun :: Env -> Id -> Err ([Type],Type)
lookupFun (sigs, cons) x = case Map.lookup x sigs of
                            Nothing -> fail $ "Unknown function " ++ printTree x ++ "."
                            Just t -> return t

addScope :: Env -> Env
addScope (sigs, cons) = (sigs, (Map.empty):cons)
