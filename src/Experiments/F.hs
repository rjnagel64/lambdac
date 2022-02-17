
module Experiments.F where

-- Compile System F to something
-- Inspired by A Type-Preserving Compiler in Haskell, but without the
-- type-preserving.
--
-- * CPS
-- * Closure Conversion
-- * Hoisting
-- * etc.

data TyVar = TyVar String

data Type
  = TyVar TyVar
  | TyBool
  | TyArr Type Type
  | TyAll TyVar Type -- Only base kinds.

data TmVar = TmVar String

data Term
  = TmVar TmVar
  | TmBool Bool
  -- Idea: what if, instead of general recursion, I provided a builtin Mu and cata
  | TmRec TmVar TmVar Term
  | TmApp Term Term
  | TmTLam TyVar Term
  | TmTApp Term Type
  -- \ TmApp Term Term
  -- \ TmLam TmVar Type Term
  -- \ TmTApp Term Type
  -- \ TmTLam TyVar Term

data KVar = KVar String

data TermK -- e
  = LamK TmVar KVar CPS
  | JumpK KVar _
  | LetValK TmVar ValueK TermK
  -- \ LetPrimK TmVar ValueK PrimOp ValueK TermK
  | AppK ValueK [TypeK] ValueK
  | IfK ValueK TermK TermK
  | HaltK ValueK

data ValueK -- v
  = BoolK Bool
  | VarK TmVar
  | 

data TypeK -- τ
  -- ∀α+. τ -> 0
  = ContK [TyVar] TypeK
  | 

cps :: Term -> (ValueK -> TermK) -> TermK
cps (TmVar x) k = k (VarK x)
cps (TmApp e1 e2) k = cps e1 (\v1 -> cps e2 (\v2 -> AppK v1 [] _))

cpsType :: Type -> Type
cpsType (TyArr a b) = TyArr a ((TyArr b TyVoid) TyVoid)
