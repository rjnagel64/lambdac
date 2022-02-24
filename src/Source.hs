
module Source
  ( Term(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  ) where

-- | Term variables stand for values
newtype TmVar = TmVar String
  deriving (Eq, Ord)

-- | Continuation variables name basic blocks and jump targets.
newtype CoVar = CoVar String
  deriving (Eq, Ord)


-- TODO: Add booleans and if-expressions. They can be compiled more efficiently
-- than case analysis on Either () ().
data Term
  -- x
  = TmVarOcc TmVar
  -- case e of inl x -> e1; inr y -> e2
  | TmCase Term TmVar Term TmVar Term
  -- inl e
  | TmInl Term
  -- inr e
  | TmInr Term
  -- \x.e
  | TmLam TmVar Term
  -- e1 e2
  | TmApp Term Term
  -- (e1, e2)
  | TmPair Term Term
  -- fst e
  | TmFst Term
  -- snd e
  | TmSnd Term
  -- let x = e1 in e2
  | TmLet TmVar Term Term
  -- let rec fs+ in e
  | TmRecFun [TmFun] Term
  -- ()
  | TmNil
  -- 17
  | TmInt Int
  -- e1 + e2
  | TmAdd Term Term
  -- iszero e
  | TmIsZero Term

-- TODO: More primops.
-- let y = primop(x+) in e
-- LetPrimK :: TmVar -> PrimOp -> TermK -> TermK
-- data PrimOp = PrimAddInt32 TmVar TmVar
--
-- Are there primops that take CoVar:s? Probably.
--
-- Just do it. The code duplication is unavoidable.


-- f x := e
data TmFun = TmFun TmVar TmVar Term

data Type
  = TySum Type Type
  | TyProd Type Type
  | TyArr Type Type
  | TyUnit

