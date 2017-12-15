module Interpreter where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import AbsMini
import PrintMini
import ErrM

data Value = VInt Integer | VDouble Double | VBool Bool | VVoid | VUndef

instance Show Value where
    show (VInt i)    = show i
    show (VDouble d) = show d
    show (VBool b)   = show b
    show VVoid       = "void" -- is this correct?
    show VUndef      = "undefined"

type Env = (Sig,[Context])
type Sig = Map Id Def
type Context = Map Id Value

interpret :: Program -> IO ()
interpret (PDefs defs) = do env <- return (addDefs starterEnv defs)
                            (DFun t f _ stms) <- return (lookupFun env (Id "main"))
                            -- Maybe check that the argument list is empty??
                            -- Maybe check that the type is void??
                            execStms env stms
                            -- Alternatively call evalExp on an EApp of main.
                            return ()

-- What if two functions have the same name???
addDefs :: Env -> [Def] -> Env
addDefs env [] = env
addDefs (sigs, scopes) (def@(DFun _ f _ _):defs) =
    addDefs ((Map.insert f def sigs), scopes) defs

execStms :: Env -> [Stm] -> IO Env
execStms env [] = return env
execStms env (st:stms) = do env' <- execStm env st
                            execStms env' stms

execStm :: Env -> Stm -> IO Env
execStm env s = 
    case s of
      SExp e          -> do (env', _) <- evalExp env e
                            return env'
      SDecl _ x       -> return (addVar env x)
      SAss x e        -> do (env', val) <- evalExp env e
                            return (setVar env' x val)
      SBlock stms     -> do env' <- execStms (enterScope env) stms
                            return (leaveScope env')
      SPrint e        -> do (env', val) <- evalExp env e
                            print val
                            return env'

evalExp :: Env -> Exp -> IO (Env, Value)
evalExp env e = 
    case e of
      EVar x         -> return (env, lookupVar env x)
      EInt i         -> return (env, VInt i)
      EDouble d      -> return (env, VDouble d)
      EAdd e1 e2     -> do (_, v1) <- evalExp env e1
                           (_, v2) <- evalExp env e2
                           case (v1,v2) of
                              (VInt i1, VInt i2)       -> return (env, VInt (i1+i2))
                              (VDouble d1, VDouble d2) -> return (env, VDouble (d1+d2))
      -- Pseudocode
      EApp f es      -> do (DFun _ f args stms) <- return (lookupFun env f)
                           env' <- loadArgs (enterScope env) env es args
                           env'' <- execStms env' stms
                           return ((leaveScope env''), VVoid)

loadArgs :: Env -> Env -> [Exp] -> [Arg] -> IO Env
loadArgs env env' [] [] = return env
loadArgs env env' (e:es) ((ADecl _ x):args) = do
  (env'', v) <- evalExp env' e
  loadArgs (setVar (addVar env x) x v) env'' es args

starterEnv :: Env
starterEnv = (starterSig, [Map.empty])

starterSig :: Sig
starterSig = Map.empty
-- Insert the built-in functions???

addVar :: Env -> Id -> Env
-- Add functionality to add multiple variables???
-- If a variable already has been declared this error is caught by the type checker
addVar (sigs, (scope:rest)) x = (sigs, ((Map.insert x VUndef scope):rest))
-- In case there is only one scope
addVar (sigs, scope) x = (sigs, [(Map.insert x VUndef (head scope))])

setVar :: Env -> Id -> Value -> Env
setVar (_, []) x _ = error $ "Unknown variable " ++ printTree x ++ "."
-- The variable is not in this context
-- setVar (sigs, ((Map.empty):rest)) x v = let (sigs', rest') = setVar (sigs, rest) x v
--                                           in (sigs', (Map.empty):rest')
-- The current context is not empty -> look for the variable and update if found.
setVar (sigs, (scope:rest)) x v = case Map.lookup x scope of
    Just _  -> (sigs, (Map.insert x v scope):rest)
    Nothing -> let (sigs', rest') = setVar (sigs, rest) x v
                in (sigs', scope:rest')

lookupVar :: Env -> Id -> Value
lookupVar (_, []) x = error $ "Uninitialized variable " ++ printTree x ++ "."
lookupVar (sigs, (scope:rest)) x = case Map.lookup x scope of
                                     Nothing -> lookupVar (sigs, rest) x
                                     Just v  -> v

-- Add function lookupFun ???
lookupFun :: Env -> Id -> Def
lookupFun (sigs, _) f = case Map.lookup f sigs of
    Nothing  -> error $ "Unknown function " ++ printTree f ++ "."
    Just def -> def

enterScope :: Env -> Env
enterScope (sigs, cons) = (sigs, (Map.empty):cons)

leaveScope :: Env -> Env
leaveScope (sigs, (_:cons)) = (sigs, cons)