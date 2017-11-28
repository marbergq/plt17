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

starterSig :: Sig
starterSig = --Map.insert printInt ([Type_int],Type_void) $
           --Map.insert printDouble ([Type_bool],Type_void) $
           --Map.insert readInt ([],Type_int) $
          -- Map.insert readDouble ([], Type_bool) 
          (Map.empty)

{-map (\(f,(a,t)) -> Map.insert (f,(a,t)) Map.empty) [printInt ([int],void),
printDouble ([doube],void),
readInt ([],int),
readDouble ([],double)]-}

checkStms :: Env -> [Stm] -> Err ()
checkStms env []        = return ()
checkStms env (st:stms) = do env' <- checkStm env st
                             checkStms env' stms

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

checkExp :: Env -> Exp -> Type -> Err ()
checkExp env e t = 
    do t' <- inferExp env e
       if t' /= t 
         then fail (printTree e ++ " has type " ++ printTree t'
                    ++ " expected " ++ printTree t)
         else return ()

inferExp :: Env -> Exp -> Err Type
inferExp env e = 
    case e of
      EId x          -> lookupVar env x
      EInt _         -> return Type_int
      EDouble _      -> return Type_double
--Type_bool Type_void
      EAdd e1 e2     -> do t1 <- inferExp env e1
                           t2 <- inferExp env e2
                           if t1 == t2 
                             then return t1
                             else fail (printTree e1 ++ " has type " 
                                         ++ printTree t1 ++ " but " 
                                         ++ printTree e2 ++ " has type " 
                                         ++ printTree t2)

--inferExp :: Env -> Exp -> Err Type
--inferExp env x = case x of
--  ETrue          -> return Type_bool
--  --EFalse         -> return Type_bool
--  EInt n         -> return Type_int
--  --EBool          -> return Type_double
--  EId id         -> return Type_id
--  EAdd exp1 exp2 -> inferBin 
--                    [Type_int , Type_double ,Type_string ]
--                    env exp1 exp2


starterEnv :: Env
starterEnv = (starterSig, [])

addVar :: Env -> Id -> Type -> Err Env
addVar (sig, scope:rest) x t = 
    case lookup x scope of
      Nothing -> return (((x,t):scope):rest) --TODO
      Just _  -> fail ("Variable " ++ printTree x ++ " already declared.")

lookupVar :: Env -> Id -> Err Type
lookupVar (_, []) x           = fail $ "Unknown variable " ++ printTree x ++ "."
lookupVar (sig, scope:rest) x = case Map.lookup x scope of
                             Nothing -> lookupVar (sig, rest) x
                             Just t  -> return t

--scope also refered to as context
addScope :: Env -> Env
addScope (sig, scopes) = (sig, [Map.empty]:scopes)