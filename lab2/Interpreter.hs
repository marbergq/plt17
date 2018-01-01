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
-- possibly these two as well:
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

{-
The variable ret_val' is used when interpreting return statements SReturn.

Everytime an EApp (function call) expression is encountered a new scope is
added to the environment and to this new scope a variable with identifier
ret_val' is added.

The value of ret_val' is VUndef until the first return statement is encountered.

It is always correct to change the value of the outermost ret_val' variable
found in the environment since any return statement is associated with the
closest function call.

The identifier ret_val' can be used because the character ' cannot be used in
the language we're interpreting. No name clashes will occur.
-}

execStms :: Env -> [Stm] -> IO (Env, Value)
execStms env [] = return (env, VVoid)
-- If a return statement has been encountered as the previous statement then
-- don't execute the following statements st and stms.
execStms env (st:stms) = case lookupVar env (Id "ret_val'") of
                           VUndef -> do (env', val) <- execStm env st
                                        execStms env' stms
                           val    -> return (env, val)

execStm :: Env -> Stm -> IO (Env, Value)
execStm env s = 
    case s of
      SExp e          -> evalExp env e
      SDecls _ []     -> return (env, VVoid)
      SDecls t (x:xs) -> execStm (addVar env x) (SDecls t xs)

      -- Change: Pass env' (output from evalExp) to addVar according to rule in
      -- the PLT textbook. /Johan
      SInit _ x e     -> do (env', val) <- evalExp env e
                            return (setVar (addVar env' x) x val, VVoid)
      
      -- Encountering SReturn changes the variable ret_val' from VUndef to the
      -- value of expression e.
      -- ret_val' with a defined value is caught by the function execStms by
      -- pattern matching /Johan
      SReturn e       -> return $ setVar env (Id "ret_val'") (evalExp env e)

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
      -- Maybe "true"/"false" is needed after ETrue/EFalse or just _ /Johan
      ETrue          -> return (env, VBool True)
      EFalse         -> return (env VBool False)
      EInt i         -> return (env, VInt i)
      EDouble d      -> return (env, VDouble d)
      EId x          -> return (env, lookupVar env x)
      EApp f xs      -> do (_ _ args stms) <- lookupFun env f
                           -- Create variable ret_val' (description above). /Johan
                           env' <- setArgs (addVar (enterScope env) (Id "ret_val'")) args xs
                           env'' <- execStms env' stms
                           return (leaveScope env', VVoid) 
                           where (DFun t f args stms) = lookupFun env f 
                           --vilket vädre ska funktionsanrop retunera? (t,_) i args. 
                           --hur får man det från execStms?                        
      -- The four built-in functions can be hard coded as special cases of EApp
      -- in this function evalExp (according to labPM).

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
-- I implemented the solution from addSetVar to check if the variable is already
-- declared. /Johan
addVar (sigs, (scope:rest)) id = case Map.lookup id scope of 
    Just _  -> "Variable " ++ printTree id ++ " already declared"
    Nothing -> (sigs, ((Map.insert id VUndef scope):rest))

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
    Just _  -> error $ "Variable " ++ printTree x ++ " already declared"
    Nothing -> (sigs, ((Map.insert x v scope):rest))

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
-- lookupVar can output the value VUndef.
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
