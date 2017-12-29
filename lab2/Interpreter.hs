module Interpreter where

import Control.Monad
--import System.Environment (getArgs)
-- Possibly this one too:
import System.Exit (exitFailure)

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM
-- possylby these two as well:
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
type Sig = Map Id Def
type Context = Map Id Value

--DOES NOT HAVE RETURN TYPE FOR ERRORS
interpret :: Program -> IO ()
interpret (PDefs defs) = --case (lookupFun (addDefs starterEnv defs) 
                         --                (Id "main")) of 
                         --       (DFun VVoid f [] stms) -> do 
                         --                           execStms env stms
                         --                           return ()
                         --       (DFun _ _ _ _)      -> fail $ "Error in main function. Either a nonempty argument list or return type is not void. "
                         --       error s                -> fail $ "Program missing main function" ++ s 
                         do env <- return (addDefs starterEnv defs)
                            (DFun t f _ stms) <- return
                                                (lookupFun env (Id "main"))
                            execStms env stms
                            return ()

execStms :: Env -> [Stm] -> IO (Env, Value)
execStms env [] = return (env, VVoid) --NOT VOID ALWAYS
execStms env (st:stms) = do (env', val) <- execStm env st
                            execStms env' stms

execStm :: Env -> Stm -> IO (Env, Value)
execStm env s = 
    case s of
      SExp e          -> evalExp env e
      SDecls _ []     -> return (env, VVoid)
      SDecls t (x:xs) -> execStm (addVar env x) (SDecls t xs)
      SInit _ x e     -> do (_, val) <- evalExp env e
                            return (setVar (addVar env x) x val, VVoid )
      SReturn e       -> evalExp env e --Hur avbryter vi all exekevering? 
      SWhile eCon s   -> do (env', VBool b) <- evalExp env eCon
                            if (b == False)
                               then return (env', VVoid)
                               else do (env'', _) <- execStm env' s
                                       execStm env'' (SWhile eCon s)
      --enter scope in first iteration of while loop and exit scope after last iteration
      SBlock stms     -> do (env', _) <- execStms (enterScope env) stms
                            return (leaveScope env', VVoid)
      SIfElse eCon sI sE -> do (env', VBool b) <- evalExp env eCon
                               if (b == True)
                                  then execStm (enterScope env') sI
                                  else do execStm (enterScope env') sE

evalExp :: Env -> Exp -> IO (Env, Value)
evalExp env e = 
    case e of
      --ETrue
      --EFalse
      EInt i         -> return (env, VInt i)
      EDouble d      -> return (env, VDouble d)
      EId x          -> return (env, lookupVar env x)
      EApp f xs      -> do env' <- setArgs (enterScope env) args xs
                           env'' <- execStms env' stms
                           return (leaveScope env', VVoid) 
                           where (DFun t f args stms) = lookupFun env f 
                           --vilket vädre ska funktionsanrop retunera? (t,_) i args. 
                           --hur får man det från execStms?                        
      --EPostIncr
      --EPostDecr
      --EPreIncr
      --EPreDecr
      --ETimes
      --EDiv
      EPlus e1 e2     -> do (_, v1) <- evalExp env e1
                            (_, v2) <- evalExp env e2
                            case (v1,v2) of
                              (VInt i1, VInt i2)       -> return (env, VInt (i1+i2) )
                              (VDouble d1, VDouble d2) -> return (env, VDouble (d1+d2) )
      --EMinus
      --ELt
      --EGt
      --ELtEq
      --EGtEq
      --EEq
      --ENEq
      --EAnd
      --EOr
      --EAss

addDefs :: Env -> [Def] -> Env
addDefs env [] = env
addDefs (sigs, scopes) (def@(DFun _ f _ _):defs) =
    addDefs ((Map.insert f def sigs), scopes) defs

starterEnv :: Env
starterEnv = (starterSig, [Map.empty])

starterSig :: Sig
starterSig = Map.empty
--starterSig = Map.insert (Id "printInt")
--                         (DFun Type_void (Id "printInt")
--                          [ADecl Type_int (Id "x")] [???]) $
--             --Map.insert (Id "printDouble") ([Type_bool],Type_void) $
--             --Map.insert (Id "readInt") ([],Type_int) $
--             --Map.insert (Id "readDouble") ([], Type_bool) 
--             (Map.empty)

addVar :: Env -> Id -> Env
addVar (sigs, (scope:rest)) x = (sigs, ((Map.insert x VUndef scope):rest))
--kanske checka att var:en inte redan är deklareread?
--titta på lösningen i addSetVar 

-- DOES NOT HAVE RETURN TYPE FOR ERRORS
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

addSetVar :: Env -> Id -> Value -> Env
addSetVar (sigs, (scope:rest)) x v = case Map.lookup x scope of
    Just _  -> error $ "Variable " ++ printTree x ++ "already declared"
    Nothing -> (sigs, (Map.insert x v scope):rest)

-- DOES NOT HAVE RETURN TYPE FOR ERRORS
setArgs :: Env -> [Arg] -> [Exp] -> IO Env
setArgs env [] [] = return env
setArgs env ((ADecl t a):args) (x:xs) = 
    do (_, val) <- evalExp env x
       setArgs (addSetVar env a val) args xs
    --minns inte varför jag tyckte vi borde gjort så här:
    --case evalExp env x of
    --   Just (_, val) -> setArgs $ env' (setVar env a val) xs
    --   _             -> error "wrong function parameter"
--setArgs env _ _ = error "function applied to wrong amount of arguments"
-- or is this part of the type checker? 

-- DOES NOT HAVE RETURN TYPE FOR ERRORS
lookupVar :: Env -> Id -> Value
lookupVar (_, []) x = error $ "Uninitialized variable " ++ printTree x ++ "."
lookupVar (sigs, (scope:rest)) x = case Map.lookup x scope of
                                     Nothing -> lookupVar (sigs, rest) x
                                     Just v  -> v

-- DOES NOT HAVE RETURN TYPE FOR ERRORS
lookupFun :: Env -> Id -> Def
lookupFun (sigs, _) f = case Map.lookup f sigs of
    Nothing  -> error $ "Unknown function " ++ printTree f ++ "."
    Just def -> def

enterScope :: Env -> Env
enterScope (sigs, scopes) = (sigs, (Map.empty):scopes)

leaveScope :: Env -> Env
leaveScope (sigs, (_:scopes)) = (sigs, scopes)
