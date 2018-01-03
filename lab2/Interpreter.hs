module Interpreter where

import Control.Monad
--import System.Exit (exitFailure)

import Data.Map (Map)
import qualified Data.Map as Map

import CPP.Abs
import CPP.Print
import CPP.ErrM

data Value = VInt Integer | VDouble Double | VBool Bool | VVoid | VUndef

instance Show Value where
    show (VInt i)    = show i
    show (VDouble d) = show d
    show (VBool b)   = show b
    show VVoid       = "void"
    show VUndef      = "undefined"

type Env = (Sig,[Context])
type Sig = Map Id Def
type Context = Map Id Value

interpret :: Program -> IO ()
interpret (PDefs defs) = let env = (addDefs starterEnv defs) in do 
  (DFun _ f [] stms) <- lookupFun env (Id "main")
  (addVar env (Id "ret_val'")) >>= (\x -> execStms x stms)
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
execStms env (st:stms) = case reachedReturn env of 
                           (False, _) -> do env' <- execStm env st
                                            execStms env' stms
                           (True, v)  -> return (env, v)
{- 
If a return statement has been encountered as the previous statement then
don't execute the following statements st and stms.
-}

execStm :: Env -> Stm -> IO Env
execStm env s = 
    case s of
      SExp e             -> do (env', val) <- evalExp env e
                               return env'
      SDecls _ []        -> return env
      SDecls t (id:ids)  -> do env' <- addVar env id
                               execStm env' (SDecls t ids)
      SInit _ id e       -> do (env', val) <- evalExp env e
                               addSetVar env' id val
{-
Encountering SReturn changes the variable ret_val' from VUndef to the
value of expression e.
ret_val' with a defined value is caught by the function execStms by
pattern matching /Johan
-}
      SReturn e          -> do (env', val) <- evalExp env e
                               -- putStrLn $ "val of x: " ++ show val
                               setVar env' (Id "ret_val'") val
      SWhile eCon s      -> do (env', VBool b) <- evalExp env eCon
                               case b of 
                                 False -> return env'
                                 _     -> case s of
                                            SBlock _ -> 
                                               do env'' <- execStm env' s
                                                  execStm env'' (SWhile eCon s)
                                            _        -> 
                                               do env'' <- execStm (enterScope env') s
                                                  execStm (leaveScope env'') (SWhile eCon s)
      SBlock stms        -> do (env', _) <- execStms (enterScope env) stms
                               return $ leaveScope env'
      SIfElse eCon sI sE -> do (env', VBool b) <- evalExp env eCon
                               if (b == True)
                                  then case sI of
                                    SBlock _ -> execStm env' sI
                                    _ -> do env'' <- execStm (enterScope env') sI
                                            return $ leaveScope env''
                                  else case sE of
                                    SBlock _ -> execStm env' sE
                                    _ -> do env'' <- execStm (enterScope env') sE
                                            return $ leaveScope env''

evalExp :: Env -> Exp -> IO (Env, Value)
evalExp env e = 
    case e of
      ETrue            -> return (env, VBool True)
      EFalse           -> return (env, VBool False)
      EInt i           -> return (env, VInt i)
      EDouble d        -> return (env, VDouble d)
      EId id           -> do val <- lookupVar env id
                             return (env, val)

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
        _                -> do (DFun _ _ args stms) <- lookupFun env f
                               {- Create variable ret_val' (description above). /Johan-}
                               freshEnv <- addVar (enterScope env) (Id "ret_val'")
                               (freshEnv', oldEnv') <- setArgs freshEnv env xs args
                               (_, val) <- execStms freshEnv' stms
                               return (oldEnv', val)
      EPostIncr x      -> do v <- lookupVar env x 
                             case v of
                               VInt i    -> do env' <- setVar env x (VInt (i+1))
                                               return (env', VInt i)
                               VDouble d -> do env' <- setVar env x (VDouble (d+1))
                                               return (env', VDouble d)
      EPostDecr x      -> do v <- lookupVar env x 
                             case v of
                               VInt i    -> do env' <- setVar env x (VInt (i-1))
                                               return (env', VInt i)
                               VDouble d -> do env' <- setVar env x (VDouble (d-1))
                                               return (env', VDouble d)
      EPreIncr x       -> do v <- lookupVar env x 
                             case v of
                               VInt i    -> do env' <- setVar env x (VInt (i+1))
                                               return (env', VInt (i+1))
                               VDouble d -> do env' <- setVar env x (VDouble (d+1))
                                               return (env', VDouble (d+1))
      EPreDecr x       -> do v <- lookupVar env x 
                             case v of
                               VInt i    -> do env' <- setVar env x (VInt (i-1))
                                               return (env', VInt (i-1))
                               VDouble d -> do env' <- setVar env x (VDouble (d-1))
                                               return (env', VDouble (d-1))
      ETimes e1 e2     -> do (v1, v2, env'') <- twiceEval env e1 e2 
                             case (v1,v2) of
                               (VInt i1, VInt i2)       -> return (env'', VInt (i1 * i2) )
                               (VDouble d1, VDouble d2) -> return (env'', VDouble (d1 * d2) ) 
      EDiv e1 e2       -> do (v1, v2, env'') <- twiceEval env e1 e2
                             case (v1,v2) of
                               (VInt i1, VInt i2)       -> return (env'', VInt (i1 `div` i2 ) )
                               (VDouble d1, VDouble d2) -> return (env'', VDouble (d1 / d2) ) 
                               {-agreed both div and / has a sufficient error handling for division by zero-}
      EPlus e1 e2      -> do (v1, v2, env'') <- twiceEval env e1 e2
                             case (v1,v2) of
                               (VInt i1, VInt i2)       -> return (env'', VInt (i1+i2) )
                               (VDouble d1, VDouble d2) -> return (env'', VDouble (d1+d2) )
      EMinus e1 e2     -> do (v1, v2, env'') <- twiceEval env e1 e2
                             case (v1,v2) of
                               (VInt i1, VInt i2)       -> return (env'', VInt (i1-i2) )
                               (VDouble d1, VDouble d2) -> return (env'', VDouble (d1-d2) )
      ELt e1 e2        -> do (v1, v2, env'') <- twiceEval env e1 e2
                             return (env'', VBool (compareVal v1 v2 "<" ))
      EGt e1 e2        -> do (v1, v2, env'') <- twiceEval env e1 e2
                             return (env'', VBool (compareVal v1 v2 ">" ))
      ELtEq e1 e2      -> do (v1, v2, env'') <- twiceEval env e1 e2
                             return (env'', VBool (compareVal v1 v2 "<=" ))
      EGtEq e1 e2      -> do (v1, v2, env'') <- twiceEval env e1 e2
                             return (env'', VBool (compareVal v1 v2 ">=" ))
      EEq e1 e2        -> do (v1, v2, env'') <- twiceEval env e1 e2
                             return (env'', VBool (compareVal v1 v2 "==" ))
      ENEq e1 e2       -> do (v1, v2, env'') <- twiceEval env e1 e2
                             return (env'', VBool (compareVal v1 v2 "/=" ))
      EAnd e1 e2       -> do (env', val) <- evalExp env e1
                             case val of
                               VBool True -> evalExp env' e2
                               _          -> return (env', val)
      EOr e1 e2        -> do (env', VBool v1) <- evalExp env e1
                             if (v1 == True)
                               then return (env', VBool v1)
                               else do (env'', v2) <- evalExp env' e2
                                       return (env'', v2)
      EAss id e        -> do (env', val) <- evalExp env e
                             env'' <- setVar env' id val
                             return (env'', val)

twiceEval :: Env -> Exp -> Exp -> IO (Value, Value, Env)
twiceEval env e1 e2 = do (env', v1) <- evalExp env e1
                         (env'', v2) <- evalExp env' e2
                         return (v1, v2, env'')

compareVal :: Value -> Value -> String -> Bool
compareVal v1 v2 op =
  case v1 of 
    VInt i1 -> case v2 of 
      VInt i2 -> intApplyBinary i1 i2 op
    VDouble d1 -> case v2 of 
      VDouble d2 -> doubleApplyBinary d1 d2 op
    VBool b1 -> case v2 of
      VBool b2 -> boolApplyBinary b1 b2 op

--Not sure how to polymorficly decide int, double or bool. sorry for ugly code.
intApplyBinary :: Integer -> Integer -> String -> Bool
intApplyBinary i1 i2 op
    | op == "<"  = i1 < i2
    | op == ">"  = i1 > i2
    | op == "<=" = i1 <= i2
    | op == ">=" = i1 >= i2
    | op == "==" = i1 == i2
    | op == "/=" = i1 /= i2

doubleApplyBinary :: Double -> Double -> String -> Bool
doubleApplyBinary d1 d2 op
    | op == "<"  = d1 < d2
    | op == ">"  = d1 > d2
    | op == "<=" = d1 <= d2
    | op == ">=" = d1 >= d2
    | op == "==" = d1 == d2
    | op == "/=" = d1 /= d2

boolApplyBinary :: Bool -> Bool -> String -> Bool
boolApplyBinary b1 b2 op
    | op == "<"  = b1 < b2
    | op == ">"  = b1 > b2
    | op == "<=" = b1 <= b2
    | op == ">=" = b1 >= b2
    | op == "==" = b1 == b2
    | op == "/=" = b1 /= b2

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

addVar :: Env -> Id -> IO Env
addVar (sigs, (scope:rest)) id = case Map.lookup id scope of 
    Just _  -> fail $ "Variable " ++ printTree id ++ " already declared"
    Nothing -> return (sigs, ((Map.insert id VUndef scope):rest))

setVar :: Env -> Id -> Value -> IO Env
setVar (_, []) id _              = fail $ "Unknown variable " ++ printTree id ++ "."
setVar (sigs, (scope:rest)) id v = case Map.lookup id scope of
    Just _  -> return (sigs, (Map.insert id v scope):rest)
    Nothing -> do (sigs', rest') <- setVar (sigs, rest) id v
                  return (sigs', scope:rest')

addSetVar :: Env -> Id -> Value -> IO Env
addSetVar (sigs, (scope:rest)) id v = case Map.lookup id scope of
    Just _  -> fail $ "Variable " ++ printTree id ++ " already declared"
    Nothing -> return (sigs, ((Map.insert id v scope):rest))

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
  (oldEnv', v) <- evalExp oldEnv e
  freshEnv' <- addSetVar freshEnv id v
  setArgs freshEnv' oldEnv' es args

lookupVar :: Env -> Id -> IO Value
lookupVar (_, []) id              = fail $ "Uninitialized variable " ++ printTree id ++ "."
lookupVar (sigs, (scope:rest)) id = case Map.lookup id scope of
                                      Nothing     -> lookupVar (sigs, rest) id
                                      Just VUndef -> fail $ "Uninitialized variable " ++ printTree id ++ "."
                                      Just v      -> return v

reachedReturn :: Env -> (Bool, Value)
reachedReturn (_, [])              = (False, VUndef )
reachedReturn (sigs, (scope:rest)) = case Map.lookup (Id "ret_val'") scope of
                                       Nothing     -> reachedReturn (sigs, rest)
                                       Just VUndef -> (False, VUndef)
                                       Just v      -> (True, v)

lookupFun :: Env -> Id -> IO Def
lookupFun (sigs, _) f = case Map.lookup f sigs of
    Nothing  -> fail $ "Unknown function " ++ printTree f ++ "."
    Just def -> return def

enterScope :: Env -> Env
enterScope (sigs, scopes) = (sigs, (Map.empty):scopes)

leaveScope :: Env -> Env
leaveScope (sigs, (_:scopes)) = (sigs, scopes)