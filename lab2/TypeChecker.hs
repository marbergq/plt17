{-
This is our beginning of a type checker. It is not finished and doesn't work
yet.
-}

module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Env = (Sig,[Context])      -- functions and context stack
type Sig = Map Id ([Type],Type) -- function type signature
type Context = Map Id Type      -- variables with their types

typecheck :: Program -> Err ()
typecheck (PDefs defs) =
  checkDefs (listFunDefs starterSig defs, [Map.empty]) defs

-- This function initializes the signature symbol table
listFunDefs :: Sig -> [Def] -> Sig
listFunDefs sigs []                         = sigs
listFunDefs sigs ( (DFun t f args _):funs ) =
    listFunDefs (Map.insert f 
                            ((reverse (listTypes [] args)), t)
                            sigs
                 )
                 funs

listTypes :: [Type] -> [Arg] -> [Type]
listTypes list []               = list
listTypes list ((ADecl t _):args) = listTypes (t:list) args

checkDefs :: Env -> [Def] -> Err ()
checkDefs env [] = return ()
checkDefs env (def:defs) = case checkDef env def of
                              Bad err -> fail err
                              Ok _ -> checkDefs env defs

checkDef :: Env -> Def -> Err ()
checkDef env (DFun t f args stms) = case addArgs (addScope env) args of
                                      Bad err -> fail ("In function " ++ (show f) ++ ": " ++ err)
                                      Ok env' -> checkStms env' stms

addArgs :: Env -> [Arg] -> Err Env
addArgs env [] = Ok env
addArgs env ((ADecl t id):args) = case addVar env [id] t of
                                    Bad err -> fail ("Variable declared twice in argument list. " ++ err)
                                    Ok env' -> addArgs env' args

checkStm :: Env -> Stm -> Err Env
checkStm env s = 
    case s of
        SExp e          -> do inferExp env e
                              return env
        SDecls t ids    -> addVar env ids t
        SInit t id e    -> do t <- inferExp env e
                              addVar env [id] t
        SBlock stms     -> do checkStms (addScope env) stms
                              return env



-- checkStm :: Env -> Type -> Stm -> Err Env
-- checkStm env val x = case x of
--     SExp exp -> do
--         inferExp env exp
--         return exp
--     SDecl typ x ->
--         updateVar env id typ
--     SWhile exp stm -> do
--         checkExp env Type_bool exp
--         checkStm env val stm

checkStms :: Env -> [Stm] -> Err ()
checkStms env [] = return ()
checkStms env (st:stms) = do env' <- checkStm env st
                             checkStms env' stms

-- checkStms :: Env -> [Stm] -> Err Env
-- checkStms env stms = case stms of
--     [] -> return env
--     x : rest -> do 
--         env' <- checkStm env x
--         checkStms env' rest

inferExp :: Env -> Exp -> Err Type
inferExp env e = 
    case e of
      EId x         -> lookupVar env x
      EInt _         -> return Type_int
      EDouble _      -> return Type_double
      ETrue          -> return Type_bool
      EFalse         -> return Type_bool
      -- EPlus e1 e2     -> do t1 <- inferExp env e1
      --                      t2 <- inferExp env e2
      --                      if t1 == t2 
      --                        then return t1
      --                        else fail (printTree e1 ++ " has type " ++ printTree t1
      --                                    ++ " but " ++ printTree e2 
      --                                    ++ " has type " ++ printTree t2)
      EPlus e1 e2    -> inferBin [Type_int, Type_double] env e1 e2
      EAss id e      -> do t <- lookupVar env id
                           checkExp env e t
                           return t

-- inferExp :: Env -> Exp -> Err Type
-- inferExp env x = case x of
--     ETrue  -> return Type_bool
--     EFalse -> return Type_bool
--     EInt n -> return Type_int
--     EDouble m -> return Type_double
--     EId id -> lookupVar env id
--     EAdd exp1 exp2 ->
--         inferBin [Type_int, Type_double] env exp1 exp2
--     EMinus exp1 exp2 ->
--         inferBin [Type_int, Type_double] env exp1 exp2
--     ETimes exp1 exp2 ->
--         inferBin [Type_int, Type_double] env exp1 exp2
--     EDiv exp1 exp2 ->
--         inferBin [Type_int, Type_double] env exp1 exp2
--     EPostIncr exp ->
--         inferMon [Type_int, Type_double] env exp
--     EPostDecr exp ->
--         inferMon [Type_int, Type_double] env exp
--     EPreIncr exp ->
--         inferMon [Type_int, Type_double] env exp
--     EPreDecr exp ->
--         inferMon [Type_int, Type_double] env exp
--     -- More steps to be added here.

-- inferMon :: [Type] -> Env -> Exp -> Err Type
-- inferMon types env exp = do
--     typ <- inferExp env exp
--         if elem typ types
--             then
--                 return typ
--             else
--                 fail $ "wrong type of expression " ++ printTree exp

inferBin :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBin types env exp1 exp2 = do
    typ <- inferExp env exp1
    if elem typ types
        then
            case checkExp env exp2 typ of
                Bad err -> fail (printTree exp1 ++ " has type " ++ printTree typ
                                 ++ " whereas " ++ err)
                Ok _ -> return typ
        else
            fail $ "wrong type of expression " ++ printTree exp1

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = 
    do t' <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return ()

-- checkExp :: Env -> Type -> Exp -> Err ()
-- checkExp env typ exp = do
--     typ2 <- inferExp env exp
--     if (typ2 = typ) then
--         return ()
--     else
--         fail $ "type of " ++ printTree exp ++
--         "expected " ++ printTree typ ++
--         "but found " ++ printTree typ2


starterEnv :: Env
starterEnv = (starterSig, [])

starterSig :: Sig
starterSig = Map.insert (Id "printInt") ([Type_int],Type_void) $
             Map.insert (Id "printDouble") ([Type_bool],Type_void) $
             Map.insert (Id "readInt") ([],Type_int) $
             Map.insert (Id "readDouble") ([], Type_bool) 
             (Map.empty)
--Probably add the built-in functions. Either here or in listFunDefs.

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

-- This function is maybe unnecessary since listFunDefs
-- does the job in the beginning.
addSig :: Env -> Id -> [Type] -> Type -> Env
addSig (sigs,cons) f args ret = (Map.insert f (args, ret) sigs, cons)