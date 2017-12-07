module Interpreter where

import Control.Monad

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

interpret :: Program -> IO ()
interpret p = putStrLn "no interpreter yet"

data Value = VInt Integer | VDouble Double | VBool Bool | VUndef

instance Show Value where
    show (VInt i)    = show i
    show (VDouble d) = show d
    show VUndef      = "undefined"

type Env = (Sig,[Context])
type Sig = Map Id ([Type],Type)
type Context = Map Id Value

interpret :: Program -> IO ()
interpret (Prog stms) = do execStms emptyEnv stms
                           return ()

execStms :: Env -> [Stm] -> IO Env
execStms env [] = return env
execStms env (st:stms) = do env' <- execStm env st
                            execStms env' stms

execStm :: Env -> Stm -> IO Env
execStm env s = 
    case s of
      SDecl _ x       -> return (addVar env x)
      SAss x e        -> return (setVar env x (evalExp env e))
      SBlock stms     -> do env' <- execStms (enterScope env) stms
                            return (leaveScope env')
      SPrint e        -> do print (evalExp env e)
                            return env

evalExp :: Env -> Exp -> Value
evalExp env e = 
    case e of
      EVar x         -> lookupVar env x
      EInt i         -> VInt i
      EDouble d      -> VDouble d
      EAdd e1 e2     -> let v1 = evalExp env e1
                            v2 = evalExp env e2
                         in case (v1,v2) of
                              (VInt i1, VInt i2)       -> VInt (i1+i2)
                              (VDouble d1, VDouble d2) -> VDouble (d1+d2)

starterEnv :: Env
starterEnv = (starterSig, [])

starterSig :: Sig
starterSig = Map.empty
-- Insert the built-in functions???

addVar :: Env -> Id -> Env
-- Add functionality to add multiple variables???
-- If a variable already has been declared this error is caught by the type checker
addVar (sigs, (scope:rest) x = (sigs, ((Map.insert x VUndef scope):rest))

setVar :: Env -> Id -> Value -> Env
setVar [] x _ = error $ "Unknown variable " ++ printTree x ++ "."
setVar ([]:rest) x v = []:setVar rest x v
setVar ((p@(y,_):scope):rest) x v 
    | y == x = ((x,v):scope):rest
    | otherwise = let scope':rest' = setVar (scope:rest) x v
                   in (p:scope'):rest'

lookupVar :: Env -> Id -> Value
lookupVar (_, []) x = error $ "uninitialized variable " ++ printTree x ++ "."
lookupVar (sigs, (scope:rest)) x = case Map.lookup x scope of
                                     Nothing -> lookupVar (sigs, rest) x
                                     Just v  -> v

-- Add function lookupFun ???

enterScope :: Env -> Env
enterScope (sigs, cons) = (sigs, (Map.empty):cons)

leaveScope :: Env -> Env
leaveScope (sigs, (_:cons)) = (sigs, cons)