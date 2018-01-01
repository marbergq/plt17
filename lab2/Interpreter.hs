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
                           VUndef -> do (env', _) <- execStm env st
                                        execStms env' stms
                           val    -> return (env, val)

execStm :: Env -> Stm -> IO (Env, Value)
execStm env s = 
    case s of
      SExp e          -> evalExp env e
      SDecls _ []     -> return (env, VVoid)
      SDecls t (id:ids) -> execStm (addVar env id) (SDecls t ids)

      -- Change: Pass env' (output from evalExp) to addVar according to rule in
      -- the PLT textbook. /Johan
      SInit _ id e     -> do (env', val) <- evalExp env e
                             return (setVar (addVar env' id) id val, VVoid)
      
      -- Encountering SReturn changes the variable ret_val' from VUndef to the
      -- value of expression e.
      -- ret_val' with a defined value is caught by the function execStms by
      -- pattern matching /Johan
      SReturn e       -> do (env', val) <- (evalExp env e)
                            return ((setVar env' (Id "ret_val'") val), VVoid)

      -- I wonder if it is correct to leave the pop the topmost scope and add a
      -- new one everytime we enter a new iteration. Maybe it is... /Johan
      SWhile eCon s   -> do (env', VBool b) <- evalExp env eCon
                            if (b == False)
                              then return (env', VVoid)
                              else case s of
                                SBlock _ -> do (env'', _) <- execStm env' s
                                               execStm env'' (SWhile eCon s)
                                -- When the body is a single statement. /Johan
                                _ -> do (env'', _) <- execStm (enterScope env') s
                                        execStm (leaveScope env'') (SWhile eCon s)
      --enter scope in first iteration of while loop and exit scope after last iteration
      -- is that what we want to do? /Johan

      SBlock stms     -> do (env', _) <- execStms (enterScope env) stms
                            return (leaveScope env', VVoid)
      
      SIfElse eCon sI sE -> do (env', VBool b) <- evalExp env eCon
                               if (b == True)
                                  then case sI of
                                    SBlock _ -> execStm env' sI
                                    _ -> do (env'', _) <- execStm (enterScope env') sI
                                            return ((leaveScope env''), VVoid)
                                  else case sE of
                                    SBlock _ -> execStm env' sE
                                    _ -> do (env'', _) <- execStm (enterScope env') sE
                                            return ((leaveScope env''), VVoid)

evalExp :: Env -> Exp -> IO (Env, Value)
evalExp env e = 
    case e of
      -- Maybe "true"/"false" is needed after ETrue/EFalse or just _ /Johan
      ETrue          -> return (env, VBool True)
      EFalse         -> return (env, VBool False)
      EInt i         -> return (env, VInt i)
      EDouble d      -> return (env, VDouble d)
      EId id          -> return (env, lookupVar env id)
      EApp f xs      -> do (DFun _ _ args stms) <- return (lookupFun env f)
                           -- Create variable ret_val' (description above). /Johan
                           env' <- setArgs (addVar (enterScope env) (Id "ret_val'")) env xs args
                           (env'', val) <- execStms env' stms
                           return ((leaveScope env''), val) 
                           --vilket vädre ska funktionsanrop retunera? (t,_) i args. 
                           --hur får man det från execStms? 

                           -- The execStms has now been designed to give the
                           -- return value if a return statement has been
                           -- encountered. /Johan

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
    Just _  -> error $ "Variable " ++ printTree id ++ " already declared"
    Nothing -> (sigs, ((Map.insert id VUndef scope):rest))

-- DOES NOT HAVE RETURN TYPE FOR ERRORS
setVar :: Env -> Id -> Value -> Env
setVar (_, []) id _ = error $ "Unknown variable " ++ printTree id ++ "."
-- This case is probably not needed when we use Data.Map
-- setVar (sigs, ((Map.empty):rest)) id v = let (sigs', rest') = setVar (sigs, rest) id v
--                                           in (sigs', (Map.empty):rest')
-- The current context is not empty -> look for the variable and update if found.
setVar (sigs, (scope:rest)) id v = case Map.lookup id scope of
    Just _  -> (sigs, (Map.insert id v scope):rest)
    Nothing -> let (sigs', rest') = setVar (sigs, rest) id v
                in (sigs', scope:rest')

addSetVar :: Env -> Id -> Value -> Env
addSetVar (sigs, (scope:rest)) id v = case Map.lookup id scope of
    Just _  -> error $ "Variable " ++ printTree id ++ " already declared"
    Nothing -> (sigs, ((Map.insert id v scope):rest))

{- setArgs
The first argument of this function is the environment to be used when
executing the function body. Therefore, this environment must have a new
fresh scope.

The second argument is the environment in which the argument expressions are
evaluated. This environment should not have a fresh scope on top.
-}
setArgs :: Env -> Env -> [Exp] -> [Arg] -> IO Env
setArgs env env' [] [] = return env
setArgs env env' (e:es) ((ADecl _ id):args) = do
  (env'', v) <- evalExp env' e
  setArgs (setVar (addVar env id) id v) env'' es args

-- DOES NOT HAVE RETURN TYPE FOR ERRORS
-- lookupVar can output the value VUndef.
lookupVar :: Env -> Id -> Value
lookupVar (_, []) id = error $ "Uninitialized variable " ++ printTree id ++ "."
lookupVar (sigs, (scope:rest)) id = case Map.lookup id scope of
                                     Nothing -> lookupVar (sigs, rest) id
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
