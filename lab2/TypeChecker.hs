module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

type Sig     = Map Id ([Type], Type)
type Context = Map Id Type
type Env     = (Sig, [Context])

typecheck :: Program -> Err ()
typecheck (PDefs defs) = checkDefs ((addDefs starterSig defs), [Map.empty]) defs

addDefs :: Sig -> [Def] -> Sig
addDefs sigs []                         = sigs
addDefs sigs ( (DFun t f args _):funs ) =
    addDefs (Map.insert f ((enlistTypes [] args), t) sigs ) funs

enlistTypes :: [Type] -> [Arg] -> [Type]
enlistTypes list []                 = list
enlistTypes list ((ADecl t _):args) = enlistTypes (t:list) args

checkDefs :: Env -> [Def] -> Err ()
checkDefs env [] = return ()
checkDefs env (def:defs) = case checkDef env def of
                              Bad err -> fail err
                              Ok _ -> checkDefs env defs

checkDef :: Env -> Def -> Err ()
checkDef env (DFun t f args stms) = case addArgs (addScope env) args of
                                      Bad err -> fail ("In function " ++ show f ++ ":\n" ++ err)
                                      Ok env' -> checkStms env' stms

addArgs :: Env -> [Arg] -> Err Env
addArgs env [] = Ok env
addArgs env ((ADecl t id):args) = case addVar env [id] t of
                                    Bad err -> fail ("Vairable declared twice in argument list.\n" ++ err)
                                    Ok env' -> addArgs env' args

checkStms :: Env -> [Stm] -> Err ()
checkStms env []        = return ()
checkStms env (st:stms) = do env' <- checkStm env st
                             checkStms env' stms

--Statements 
checkStm :: Env -> Stm -> Err Env
checkStm env s = 
    case s of
      SDecls t xs       -> addVar env xs t
      SInit t id e    -> do t <- inferExp env e
                            addVar env [id] t
      SBlock stms     -> do checkStms (addScope env) stms
                            return env
      SReturn e       -> do inferExp env e
                            return env
      SExp e          -> do inferExp env e
                              return env
      --SWhile e stm    ->
      --SIfElse e stm stm ->

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = 
    do t' <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return ()

-- Expresions 
inferExp :: Env -> Exp -> Err Type
inferExp env e =
    case e of
      EInt _         -> return Type_int
      EDouble _      -> return Type_double
      ETrue          -> return Type_bool
      EFalse         -> return Type_bool
      EId x          -> lookupVar env x
      EApp f es      -> lookupFun env f es
      EPlus e1 e2    -> inferBinary [Type_int, Type_double] env e1 e2
      EMinus e1 e2   -> inferBinary [Type_int, Type_double] env e1 e2
      ETimes e1 e2   -> inferBinary [Type_int, Type_double] env e1 e2
      EDiv e1 e2     -> inferBinary [Type_int, Type_double] env e1 e2
      EAss id e      -> do t <- lookupVar env id
                           checkExp env e t
                           return t
      EOr e1 e2      -> inferBinary [Type_bool] env e1 e2
      EAnd e1 e2     -> inferBinary [Type_bool] env e1 e2
      EEq e1 e2      -> inferBinary [Type_bool] env e1 e2
      ENEq e1 e2     -> inferBinary [Type_bool] env e1 e2
      EELt. e1 e2    -> inferBinary [Type_bool] env e1 e2
      EEGt. e1 e2    -> inferBinary [Type_bool] env e1 e2
      EELtEq. e1 e2  -> inferBinary [Type_bool] env e1 e2
      EEGtEq. e1 e2  -> inferBinary [Type_bool] env e1 e2
      EPostIncr. x   -> lookupVar env x
      EPostDecr. x   -> lookupVar env x
      EPreIncr. x    -> lookupVar env x
      EPreDecr. x    -> lookupVar env x 

inferBinary :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBinary validTypes env e1 e2 = do
    t1 <- inferExp env e1
    if elem t1 validTypes
        then
            case checkExp env e2 t of
                Bad err -> fail (printTree e1 ++ " has type " ++ printTree t1
                                 ++ " whereas " ++ err)
                Ok _ -> return t1
        else
            fail $ "Cannot apply function on type " ++ printTree t1

starterEnv :: Env
starterEnv = (starterSig, [])

starterSig :: Sig
starterSig = Map.insert (Id "printInt") ([Type_int],Type_void) $
             Map.insert (Id "printDouble") ([Type_bool],Type_void) $
             Map.insert (Id "readInt") ([],Type_int) $
             Map.insert (Id "readDouble") ([], Type_bool) 
             (Map.empty)

--scope also refered to as context

addScope :: Env -> Env
addScope (sig, scopes) = (sig, (Map.empty):scopes)

addVar :: Env -> [Id] -> Type -> Err Env
addVar env [] _ = return env
addVar (sig, scope:rest) x:xs t = 
    case Map.lookup x scope of
      Nothing -> addVar (sig, ((Map.insert x t scope):rest)) xs t
      Just _  -> fail ("Variable " ++ printTree x ++ " already declared.")

lookupVar :: Env -> Id -> Err Type
lookupVar (_, []) x           = fail $ "Unknown variable " ++ printTree x ++ "."
lookupVar (sig, scope:rest) x = case Map.lookup x scope of
                             Nothing -> lookupVar (sig, rest) x
                             Just t  -> return t

--lookupFun :: Env -> Ident -> Err ([Type],Type)
--lookupFun (sigs, cons) x = case Map.lookup x sigs of
--                            Nothing -> fail $ "Unknown function " ++ printTree x ++ "."
--                            Just t -> return t

lookupFun :: Env -> Id -> [Exp] -> Err Type
lookupFun (sig, scope:rest) f e:es = case Map.lookup f sig of
                          Just (_, t) -> return t
                          Nothing     -> fail ("Function " ++ show f ++ "not declared")