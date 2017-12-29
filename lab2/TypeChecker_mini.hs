module TypeChecker where

import AbsMini
import PrintMini
import ErrM

import Data.Map (Map)
import qualified Data.Map as Map

typecheck :: Program -> Err ()
-- Change Prog to the label of the top label in the grammar.
typecheck (PDefs defs) = 
  checkDefs (listFunDefs emptySig defs, [Map.empty]) defs

--typecheck (Prog stms) = checkStms emptyEnv stms

--This call is a list of all function definitions
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
-- Maybe add a new scope.
checkDef env (DFun t f args stms) = case addArgs env args of
                                      Bad err -> fail ("In function " ++ (show f) ++ ": " ++ err)
                                      Ok env' -> checkStms env' stms

addArgs :: Env -> [Arg] -> Err Env
addArgs env [] = Ok env
addArgs env ((ADecl t id):args) = case addVar env id t of
                                    Bad err -> fail ("Variable declared twice in argument list. " ++ err)
                                    Ok env' -> addArgs env' args

checkStms :: Env -> [Stm] -> Err ()
checkStms env [] = return ()
checkStms env (st:stms) = do env' <- checkStm env st
                             checkStms env' stms

checkStm :: Env -> Stm -> Err Env
checkStm env s = 
    case s of
      SExp e          -> do inferExp env e
                            return env
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
                             else fail (printTree e1 ++ " has type " ++ printTree t1
                                         ++ " but " ++ printTree e2 
                                         ++ " has type " ++ printTree t2)
      EApp f es      -> do funType <- lookupFun env f
                           case checkArgs env es (fst funType) of
                             Bad err -> fail ("Illegal function call "
                                              ++ printTree f ++ ". " ++ err)
                             Ok _    -> return (snd funType)

type Env = (Sig,[Context])      -- functions and context stack
type Sig = Map Id ([Type],Type) -- function type signature
type Context = Map Id Type      -- variables with their types

emptyEnv :: Env
emptyEnv = (emptySig, [])

emptySig :: Sig
emptySig = Map.empty
--Probably add the built-in functions. Either here or in listFunDefs.

-- This function is used to check EApp argument list
checkArgs :: Env -> [Exp] -> [Type] -> Err ()
checkArgs env [] [] = return ()
checkArgs env [] _ = fail $ "In argument list: Too few arguments provided."
checkArgs env _ [] = fail $ "In argument list: Too many arguments provided."
checkArgs env (e:es) (t:ts) = case checkExp env e t of
                                Bad err -> fail $ "In argument list: " ++ err
                                Ok _    -> checkArgs env es ts

addVar :: Env -> Id -> Type -> Err Env
addVar (sigs, (scope:rest)) x t =
    case Map.lookup x scope of
      Nothing -> return (sigs, ((Map.insert x t scope):rest))
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

-- This function needs to be modified to fit with the new Env type.
addScope :: Env -> Env
addScope (sigs, cons) = (sigs, (Map.empty):cons)

addSig :: Env -> Id -> [Type] -> Type -> Env
addSig (sigs,cons) f args ret = (Map.insert f (args, ret) sigs, cons)