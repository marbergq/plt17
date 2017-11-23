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

-- typecheck p = return ()
typecheck :: Program -> Err ()
typecheck (PDefs defs) = do
  env <- (listFunDefs emptySig defs, [emptyContext])
  checkDefs env 

--This call is a list of all function definitions
listFunDefs :: Sig -> [Def] -> Sig
listFunDefs sigs []                         = sigs
listFunDefs sigs ( (DFun t f args _):funs ) =
    listFunDefs (Map.insert f 
                            ((listTypes [] args), t)
                            sigs
                 )
                 funs

listTypes :: [Type] -> [Arg] -> [Type]
listTypes list []               = list
listTypes list ((ADecl t _):args) = listTypes (list++t) args

checkDefs :: Env -> [Def] -> Err ()
checkDefs env [] = return ()
checkDefs env (def:defs) = do checkDef env def
                              checkDefs env defs

checkDef :: Env -> Def -> Err ()
-- Maybe add a new scope.
checkDef env (DFun t f args stms) = do env' <- addArgs env args
                                       checkStms env' stms

addArgs :: Env -> [Arg] -> Err Env
addArgs env [] = env
addArgs env ((ADecl t id):args) = addArgs (addVar env id t) args

checkStm :: Env -> Type -> Stm -> Err Env
checkStm env val x = case x of
    SExp exp -> do
        inferExp env exp
        return exp
    SDecl typ x ->
        updateVar env id typ
    SWhile exp stm -> do
        checkExp env Type_bool exp
        checkStm env val stm

checkStms :: Env -> [Stm] -> Err Env
checkStms env stms = case stms of
    [] -> return env
    x : rest -> do 
        env' <- checkStm env x
        checkStms env' rest

inferExp :: Env -> Exp -> Err Type
inferExp env x = case x of
    ETrue  -> return Type_bool
    EFalse -> return Type_bool
    EInt n -> return Type_int
    EDouble m -> return Type_double
    EId id -> lookupVar env id
    EAdd exp1 exp2 ->
        inferBin [Type_int, Type_double] env exp1 exp2
    EMinus exp1 exp2 ->
        inferBin [Type_int, Type_double] env exp1 exp2
    ETimes exp1 exp2 ->
        inferBin [Type_int, Type_double] env exp1 exp2
    EDiv exp1 exp2 ->
        inferBin [Type_int, Type_double] env exp1 exp2
    EPostIncr exp ->
        inferMon [Type_int, Type_double] env exp
    EPostDecr exp ->
        inferMon [Type_int, Type_double] env exp
    EPreIncr exp ->
        inferMon [Type_int, Type_double] env exp
    EPreDecr exp ->
        inferMon [Type_int, Type_double] env exp

inferMon :: [Type] -> Env -> Exp -> Err Type
inferMon types env exp = do
    typ <- inferExp env exp
        if elem typ types
            then
                return typ
            else
                fail $ "wrong type of expression " ++ printTree exp

inferBin :: [Type] -> Env -> Exp -> Exp -> Err Type
inferBin types env exp1 exp2 = do
    typ <- inferExp env exp1
    if elem typ types
        then
            checkExp env exp2 typ
        else
            fail $ "wrong type of expression " ++ printTree exp1

checkExp :: Env -> Type -> Exp -> Err ()
checkExp env typ exp = do
    typ2 <- inferExp env exp
    if (typ2 = typ) then
        return ()
    else
        fail $ "type of " ++ printTree exp ++
        "expected " ++ printTree typ ++
        "but found " ++ printTree typ2


-- This doesn't correspond to: type Env = (Sig,[Context])
emptyEnv :: Env
emptyEnv = (emptySig, [])

emptySig :: Sig
emptySig = Map.empty
--Probably add the built-in functions. Either here or in listFunDefs.

emptyContext :: Context
emptyContext = Map.empty

addVar :: Env -> Ident -> Type -> Err Env
addVar (sigs, (scope:rest)) x t =
    case Map.lookup x scope of
      Nothing -> return (sigs, (((x,t):scope):rest))
      Just _  -> fail ("Variable " ++ printTree x ++ " already declared.")

lookupVar :: Env -> Ident -> Err Type
lookupVar (_, []) x = fail $ "Unknown variable " ++ printTree x ++ "."
lookupVar (sigs, (scope:rest)) x = case Map.lookup x scope of
                             Nothing -> lookupVar (sigs, rest) x
                             Just t  -> return t

lookupFun :: Env -> Ident -> Err ([Type],Type)
lookupFun (sigs, cons) x = case Map.lookup x sigs of
                            Nothing -> fail $ "Unknown function " ++ printTree x ++ "."
                            Just t -> return t

-- This function needs to be modified to fit with the new Env type.
addScope :: Env -> Env
addScope (sigs, cons) = (sigs, [emptyContext]:cons)

addSig :: Env -> Ident -> [Type] -> Type -> Env
addSig (sigs,cons) f args ret = (Map.insert f (args, ret) sigs, cons)