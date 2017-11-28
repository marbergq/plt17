module TypeChecker where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

-- TYPE CHECKER --

--type Env = [[(Id, Type)]]
type Sig     = Map Id ([Type], Type)
type Context = Map Id Type  --a.k.a. env blocks
type Env     = (Sig, [Context])

--typecheck :: Program -> Err ()
--typecheck (Prog stms) = checkStms starterEnv stms
typecheck :: Program -> Err Sig
typecheck (PDefs defs) = Ok $ listFunDefs starterSig defs
--typecheck :: Program -> Err ()
--typecheck (PDefs defs) = do
--  checkDefs (listFunDefs emptySig defs, [emptyContext]) defs

listFunDefs :: Sig -> [Def] -> Sig
listFunDefs sigs []                         = sigs
listFunDefs sigs ( (DFun t f args _):funs ) =
    listFunDefs (Map.insert f 
                            ((listTypes [] args), t)
                            sigs
                 )
                 funs

listTypes :: [Type] -> [Arg] -> [Type]
listTypes list []                 = list
listTypes list ((ADecl t _):args) = listTypes (t:list) args

--checkDefs :: Env -> [Def] -> Err ()
--checkDefs env [] = return ()
--checkDefs env (def:defs) = do checkDef env def
--                              checkDefs env defs
--
--checkDef :: Env -> Def -> Err ()
---- Maybe add a new scope.
---- The return type doesn't match with addArgs.
--checkDef env (DFun t f args stms) = case addArgs env args of
--                                      Bad err -> fail err
--                                      Ok env' -> checkStms env' stms
--
--addArgs :: Env -> [Arg] -> Err Env
--addArgs env [] = Ok env
----addArgs env ((ADecl t id):args) = addArgs (addVar env id t) args
--addArgs env ((ADecl t id):args) = case addVar env id t of
--                                    Bad err -> fail err
--                                    Ok env' -> addArgs env' args

checkStms :: Env -> [Stm] -> Err ()
checkStms env []        = return ()
checkStms env (st:stms) = do env' <- checkStm env st
                             checkStms env' stms

--checkStms :: Env -> [Stm] -> Err Env
--checkStms env stms = case stms of
--    [] -> return env
--    x : rest -> do 
--        env' <- checkStm env x
--        checkStms env' rest

checkStm :: Env -> Stm -> Err Env
checkStm env s = 
    case s of
      SDecl t x       -> addVar env x t
      SAss x e        -> do t <- lookupVar env x
                            checkExp env e t
                            return env      
      SBlock stms     -> do checkStms (addScope env) stms
                            return env
      SReturn e       -> do inferExp env e
                            return env

--checkStm :: Env -> Type -> Stm -> Err Env
--checkStm env val x = case x of
--    SExp exp -> do
--        inferExp env exp
--        return exp
--    SDecl typ x ->
--        updateVar env id typ
--    SWhile exp stm -> do
--        checkExp env Type_bool exp
--        checkStm env val stm

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = 
    do t' <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return ()

--checkExp :: Env -> Type -> Exp -> Err ()
--checkExp env typ exp = do
--    typ2 <- inferExp env exp
--    if (typ2 = typ) then
--        return ()
--    else
--        fail $ "type of " ++ printTree exp ++
--        "expected " ++ printTree typ ++
--        "but found " ++ printTree typ2

inferExp :: Env -> Exp -> Err Type
inferExp env e = 
    case e of
      EId x          -> lookupVar env x
      EInt _         -> return Type_int
      EDouble _      -> return Type_double
    --  ETrue          -> return Type_bool
    --  EFalse         -> return Type_bool
    --  ?              -> return Type_void
      EAdd e1 e2     -> do t1 <- inferExp env e1
                           t2 <- inferExp env e2
                           if t1 == t2 
                             then return t1
                             else fail (printTree e1 ++ " has type " 
                                         ++ printTree t1 ++ " but " 
                                         ++ printTree e2 ++ " has type " 
                                         ++ printTree t2)
    --  EAdd exp1 exp2 -> inferBin 
    --                    [Type_int, Type_double, Type_string]
    --                    env exp1 exp2

starterEnv :: Env
starterEnv = (starterSig, [])

starterSig :: Sig
starterSig = --Map.insert printInt ([Type_int],Type_void) $
           --Map.insert printDouble ([Type_bool],Type_void) $
           --Map.insert readInt ([],Type_int) $
          -- Map.insert readDouble ([], Type_bool) 
          (Map.empty)

starterContext :: Context
starterContext = Map.empty

--scope also refered to as context
addScope :: Env -> Env
addScope (sig, scopes) = (sig, (Map.empty):scopes)

addVar :: Env -> Id -> Type -> Err Env
addVar (sig, scope:rest) x t = 
    case Map.lookup x scope of
      Nothing -> return (sig, ((Map.insert x t scope):rest))
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