module Interpreter where

import Control.Monad
-- Possibly this one too:
--import System.Environment (getArgs)
import System.Exit (exitFailure)

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM
-- possibly these two as well:
--import CPP.Lex
--import CPP.Par

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
                            execStms (addVar env (Id "ret_val'")) stms
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
execStms env (st:stms) = case reachedReturn env of 
                           (False, _) -> do (env', _) <- execStm env st
                                            execStms env' stms
                           (True, v)  -> return (env, v)

--Consider removing Value in return type. /m
execStm :: Env -> Stm -> IO (Env, Value)
execStm env s = 
    case s of
      SExp e             -> evalExp env e --fast ignorera värdet
      SDecls _ []        -> return (env, VVoid)
      SDecls t (id:ids)  -> execStm (addVar env id) (SDecls t ids)
      -- Change: Pass env' (output from evalExp) to addVar according to rule in
      -- the PLT textbook. /Johan
      SInit _ id e       -> do (env', val) <- evalExp env e
                               return (setVar (addVar env' id) id val, VVoid)
      -- Encountering SReturn changes the variable ret_val' from VUndef to the
      -- value of expression e.
      -- ret_val' with a defined value is caught by the function execStms by
      -- pattern matching /Johan
      SReturn e          -> do (env', val) <- (evalExp env e)
                               return ((setVar env' (Id "ret_val'") val), VVoid)
      SWhile eCon s      -> do (env', VBool b) <- evalExp env eCon
                               if (b == False)
                                 then return (env', VVoid)
                                 else case s of
                                   SBlock _ -> do (env'', _) <- execStm env' s
                                                  execStm env'' (SWhile eCon s)
                                   _ -> do (env'', _) <- execStm (enterScope env') s
                                           execStm (leaveScope env'') (SWhile eCon s)
      SBlock stms        -> do (env', _) <- execStms (enterScope env) stms
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
      ETrue          -> return (env, VBool True)
      EFalse         -> return (env, VBool False)
      EInt i         -> return (env, VInt i)
      EDouble d      -> return (env, VDouble d)
      EId id         -> return (env, lookupVar env id)

      EApp f xs@(x:xr) -> case f of
        Id "printInt"    -> do (env', val) <- evalExp env x
                               print val
                               return (env', VVoid)
        Id "printDouble" -> do (env', val) <- evalExp env x
                               print val
                               return (env', VVoid)
        Id "readInt"     -> do i <- readInt
                               return (env, VInt i)
        Id "readDouble"  -> do d <- readDouble
                               return (env, VDouble d)
        _  -> do (DFun _ _ args stms) <- return (lookupFun env f)
                 -- Create variable ret_val' (description above). /Johan
                 (freshEnv, oldEnv') <- setArgs (addVar (enterScope env)
                                                        (Id "ret_val'")
                                                )
                                                env xs args
                 (_, val) <- execStms freshEnv stms
                 return (oldEnv', val) 

      EPostIncr x     -> case lookupVar env x of
                            VInt i    -> return (setVar env x (VInt (i+1))   , VInt i)
                            VDouble d -> return (setVar env x (VDouble (d+1)), VDouble d)
      EPostDecr x     -> case lookupVar env x of
                            VInt i    -> return (setVar env x (VInt (i-1))   , VInt i)
                            VDouble d -> return (setVar env x (VDouble (d-1)), VDouble d)
      EPreIncr x      -> case lookupVar env x of
                            VInt i    -> return (setVar env x (VInt (i+1))   , VInt (i+1))
                            VDouble d -> return (setVar env x (VDouble (d+1)), VDouble (d+1))
      EPreDecr x      -> case lookupVar env x of
                            VInt i    -> return (setVar env x (VInt (i-1))   , VInt (i-1))
                            VDouble d -> return (setVar env x (VDouble (d-1)), VDouble (d-1))
      ETimes e1 e2    -> do (env', v1) <- evalExp env e1
                            (env'', v2) <- evalExp env' e2
                            case (v1,v2) of
                              (VInt i1, VInt i2)       -> return (env'', VInt (i1 * i2) )
                              (VDouble d1, VDouble d2) -> return (env'', VDouble (d1 * d2) ) 
      EDiv e1 e2      -> do (env', v1) <- evalExp env e1
                            (env'', v2) <- evalExp env' e2
                            case (v1,v2) of
                              (VInt i1, VInt i2)       -> return (env'', VInt (i1 `div` i2 ) )
                              (VDouble d1, VDouble d2) -> return (env'', VDouble (d1 / d2) ) 
                              --agreed both div and / has a sufficient error handling for division by zero
      EPlus e1 e2     -> do (env', v1) <- evalExp env e1
                            (env'', v2) <- evalExp env' e2
                            case (v1,v2) of
                              (VInt i1, VInt i2)       -> return (env'', VInt (i1+i2) )
                              (VDouble d1, VDouble d2) -> return (env'', VDouble (d1+d2) )
      EMinus e1 e2    -> do (env', v1) <- evalExp env e1
                            (env'', v2) <- evalExp env' e2
                            case (v1,v2) of
                              (VInt i1, VInt i2)       -> return (env'', VInt (i1-i2) )
                              (VDouble d1, VDouble d2) -> return (env'', VDouble (d1-d2) )
      --ELt
      --EGt
      --ELtEq
      --EGtEq
      --EEq
      --ENEq
      --EAnd
      EOr e1 e2       -> do (env', VBool v1) <- evalExp env e1
                            if (v1 == True)
                              then return (env', VBool v1)
                              else do (env'', v2) <- evalExp env' e2
                                      return (env'', v2)
      EAss id e       -> do (env', val) <- evalExp env e
                            return ((setVar env' id val), val)

readInt :: IO Integer
readInt = readLn

readDouble :: IO Double
readDouble = readLn

addDefs :: Env -> [Def] -> Env
addDefs env [] = env
addDefs (sigs, scopes) (def@(DFun _ f _ _):defs) =
    addDefs ((Map.insert f def sigs), scopes) defs

starterEnv :: Env
starterEnv = (starterSig, [Map.empty])

starterSig :: Sig
starterSig = Map.empty

addVar :: Env -> Id -> Env
addVar (sigs, (scope:rest)) id = case Map.lookup id scope of 
    Just _  -> error $ "Variable " ++ printTree id ++ " already declared"
    Nothing -> (sigs, ((Map.insert id VUndef scope):rest))


-- Only to be used for declared variables.
setVar :: Env -> Id -> Value -> Env
setVar (_, []) id _              = error $ "Unknown variable " ++ printTree id ++ "."
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
setArgs :: Env -> Env -> [Exp] -> [Arg] -> IO (Env, Env)
setArgs freshEnv oldEnv' [] []                     = return (freshEnv, oldEnv')
setArgs freshEnv oldEnv (e:es) ((ADecl _ id):args) = do
  (oldEnv', v) <- evalExp oldEnv e --oldEnv' captures potential side effects
  setArgs (addSetVar freshEnv id v) oldEnv' es args

lookupVar :: Env -> Id -> Value
lookupVar (_, []) id = error $ "Uninitialized variable " ++ printTree id ++ "."
lookupVar (sigs, (scope:rest)) id = case Map.lookup id scope of
                                     Nothing     -> lookupVar (sigs, rest) id
                                     Just VUndef -> error $ "Uninitialized variable " ++ printTree id ++ "."
                                     Just v      -> v

reachedReturn :: Env -> (Bool, Value)
reachedReturn (_, [])              = (False, VUndef )
reachedReturn (sigs, (scope:rest)) = case Map.lookup (Id "ret_val'") scope of
                                       Nothing     -> reachedReturn (sigs, rest)
                                       Just VUndef -> (False, VUndef)
                                       Just v      -> (True, v)

lookupFun :: Env -> Id -> Def
lookupFun (sigs, _) f = case Map.lookup f sigs of
    Nothing  -> error $ "Unknown function " ++ printTree f ++ "."
    Just def -> def

enterScope :: Env -> Env
enterScope (sigs, scopes) = (sigs, (Map.empty):scopes)

leaveScope :: Env -> Env
leaveScope (sigs, (_:scopes)) = (sigs, scopes)
