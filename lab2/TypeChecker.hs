module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

-- TYPE CHECKER --

type Env = [[(Ident, Type)]]

type Sig     = Map Id ([Type], Type)
--type Context = Map Id Type 
--type Env     = (Sig, [Context])

--typecheck :: Program -> Err ()
--typecheck (Prog stms) = checkStms emptyEnv stms
typecheck :: Program -> Err ()
typecheck (PDefs defs) = listFunDefs emptySig defs

listFunDefs :: Sig -> [Def] -> Sig
listFunDefs sigs []                            = sigs
listFunDefs sigs ( (DFun t f args stms):funs ) =
	listFunDefs (Map.insert f (args, t) sigs) funs

emptySig :: Sig
emptySig =  Map.empty
--todo add built-in funcs

checkStms :: Env -> [Stm] -> Err ()
checkStms env []        = return ()
checkStms env (st:stms) = do env' <- checkStm env st
                             checkStms env' stms

checkStm :: Env -> Stm -> Err Env
checkStm env s = 
    case s of
      SDecl t x       -> addVar env x t
      SAss x e        -> do t <- lookupVar env x
                            checkExp env e t
                            return env      
      SBlock stms     -> do checkStms (addScope env) stms
                            return env
      SPrint e        -> do inferExp env e
                            return env

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = 
    do t' <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return ()

inferExp :: Env -> Exp -> Err Type
inferExp env e = 
    case e of
      EVar x         -> lookupVar env x
      EInt _         -> return TInt
      EDouble _      -> return TDouble
      EAdd e1 e2     -> do t1 <- inferExp env e1
                           t2 <- inferExp env e2
                           if t1 == t2 
                             then return t1
                             else fail (printTree e1 ++ " has type " 
                                         ++ printTree t1 ++ " but " 
                                         ++ printTree e2 ++ " has type " 
                                         ++ printTree t2)

--inferExp :: Env -> Exp -> Err Type
--inferExp env x = case x of
--	ETrue          -> return Type_bool
--	--EFalse         -> return Type_bool
--	EInt n         -> return Type_int
--	--EBool          -> return Type_double
--	EId id         -> return Type_id
--	EAdd exp1 exp2 -> inferBin 
--	                  [Type_int , Type_double ,Type_string ]
--	                  env exp1 exp2
emptyEnv :: Env
emptyEnv = [[]]

addVar :: Env -> Ident -> Type -> Err Env
addVar (scope:rest) x t = 
    case lookup x scope of
      Nothing -> return (((x,t):scope):rest)
      Just _  -> fail ("Variable " ++ printTree x ++ " already declared.")

lookupVar :: Env -> Ident -> Err Type
lookupVar [] x           = fail $ "Unknown variable " ++ printTree x ++ "."
lookupVar (scope:rest) x = case lookup x scope of
                             Nothing -> lookupVar rest x
                             Just t  -> return t

addScope :: Env -> Env
addScope env = []:env