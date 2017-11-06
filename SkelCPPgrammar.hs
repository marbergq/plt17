module SkelCPPgrammar where

-- Haskell module generated by the BNF converter

import AbsCPPgrammar
import ErrM
type Result = Err String

failure :: Show a => a -> Result
failure x = Bad $ "Undefined case: " ++ show x

transId :: Id -> Result
transId x = case x of
  Id string -> failure x
transProgram :: Program -> Result
transProgram x = case x of
  PDefs defs -> failure x
transDef :: Def -> Result
transDef x = case x of
  DFunction type_ id args stmts -> failure x
transType :: Type -> Result
transType x = case x of
  Type_int -> failure x
  Type_bool -> failure x
  Type_char -> failure x
  Type_double -> failure x
  Type_void -> failure x
  Type_string -> failure x
  TypeQConst qconst -> failure x
transArg :: Arg -> Result
transArg x = case x of
  ADef type_ id -> failure x
transStmt :: Stmt -> Result
transStmt x = case x of
  SExp exp -> failure x
  SRet exp -> failure x
transQConst :: QConst -> Result
transQConst x = case x of
  QConstDef qcelems -> failure x
transQCElem :: QCElem -> Result
transQCElem x = case x of
  Qconstelem id -> failure x
transExp :: Exp -> Result
transExp x = case x of
  EInt integer -> failure x
  EChar char -> failure x
  EDouble double -> failure x
  EId id -> failure x
  Estring string -> failure x
  EQualConst qconst -> failure x
  ELShift exp1 exp2 -> failure x
  ERShift exp1 exp2 -> failure x
