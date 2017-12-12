module Interpreter where

import Control.Monad
--import System.Environment (getArgs)
--import System.Exit (exitFailure)

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM
-- possylby these two as well
import CPP.Lex
import CPP.Par

data Value = VInt Integer | VDouble Double | VBool Bool | VVoid | VUndef

instance Show Value where
    show (VInt i)    = show i
    show (VDouble d) = show d
    show (VBool b)   = show b
    show VVoid       = "void" -- is this correct?
    show VUndef      = "undefined"

type Env = (Sig,[Context])
type Sig = Map Id Def --What about type Sig = [(Id, [Value] -> IO Value)]
type Context = Map Id Value

--DOES NOT HAVE RETURN TYPE FOR ERRORS
interpret :: Program -> IO ()
interpret (PDefs defs) = --case (lookupFun (addDefs starterEnv defs) 
                         --                (Id "main")) of 
                         --       (DFun VVoid f [] stms) -> do 
                         --                           execStms env stms
                         --                           return ()
                         --       (DFun _ _ _ _)      -> fail $ "Error in main function. Either a nonempty argument list or return type ios not void. "
                         --       error s                -> fail $ "Program missing main function" ++ s 
                         do env <- return (addDefs starterEnv defs)
                            (DFun t f _ stms) <- return
                                                (lookupFun env (Id "main"))
                            execStms (enterScope env) stms --eller hur
                            return ()


-- What if two functions have the same name???
-- shouldn't that be handeled in the type checker?
addDefs :: Env -> [Def] -> Env
addDefs env [] = env
addDefs (sigs, scopes) (def@(DFun _ f _ _):defs) =
    addDefs ((Map.insert f def sigs), scopes) defs

--kallas bara på för en lista av stms,
--vilka bara finns i funktionernas block of stms eller i ett stmt block
--därför alltid leaveScope
execStms :: Env -> [Stm] -> IO Env
execStms env [] = return leaveScope env
execStms env (st:stms) = do env' <- execStm env st
                            execStms env' stms

execStm :: Env -> Stm -> IO Env
execStm env s = 
    case s of
      SExp e        -> return (evalExp env e)
      SDecls t x:xs -> execStms (addVar env x) (SDecls t xs)
      SDecls t []   -> return env
      SInit _ x e   -> return setVar (addVar env x) x (evalExp env e)
      SReturn e     -> return (evalExp env e) --how to actualy "return" e? (along with env)
      SWhile eCon s -> --do env' <- (evalExp env eCon) FEL för evalExp returnerar inte env
                       case (evalExp env' eCon)  of
                         False -> return env'
                         _     -> do env'' <- (execStm env' s)
                                     execStm env'' (SWhile eCon s)
      SBlock stms   -> do env' <- execStms (enterScope env) stms
                                  return env'
      SIfElse eCon sI sE -> case (evalExp env eCon) of --side effects on conditional!include new env!!
                              True -> execStm env sI
                              _    -> execStm env eE

--What about side effects? eval av exp har det i boken, vi borde väl returnera env också
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
-- yep. what if :  (as aarnes lecture)
---sig ===[(Id, [Value] -> IO Value)]
{-
(Id "printInt",   \ [v] -> putStrLn (printValue v) >> return Vvoid)
(Id "printDouble",\ [v] -> putStrLn (printValue v) >> return Vvoid)
(Id "readInt",    \ []  -> getLine >>= return . Vint . read)
(Id "readDouble", \ []  -> getLine >>= return . Vdouble . read)
-}



addVar :: Env -> Id -> Env
-- Add functionality to add multiple variables???
-- If a variable already has been declared this error is caught by the type checker
addVar (sigs, (scope:rest)) x = (sigs, ((Map.insert x VUndef scope):rest))

setVar :: Env -> Id -> Value -> Env
setVar (_, []) x _ = error $ "Unknown variable " ++ printTree x ++ "."
-- This case is probably not needed when we use Data.Map
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

lookupFun :: Env -> Id -> Def
lookupFun (sigs, _) f = case Map.lookup f sigs of
    Nothing  -> error $ "Unknown function " ++ printTree f ++ "."
    Just def -> def
-- DOES NOT HAVE RETURN TYPE FOR ERRORS

enterScope :: Env -> Env
enterScope (sigs, scopes) = (sigs, (Map.empty):scopes)

leaveScope :: Env -> Env
leaveScope (sigs, (_:scopes)) = (sigs, scopes)