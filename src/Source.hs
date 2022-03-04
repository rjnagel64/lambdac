
module Source
  ( Term(..)
  , TmVar(..)
  , TmFun(..)
  , Type(..)
  , TyVar(..)
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


-- @f x := e@, used for recursion.
-- I'm not really satisfied with this. How does a 'TmFun' interact with polymorphism?
-- How does it deal with multiple parameters? (i.e., if I allow 'TmFun' to have
-- multiple parameters, are unsaturated applications permitted?)
-- What do multiple-argument functions look like after CPS?
--
-- @let fun f x = e; in e'@ is basically @let rec f = \x -> e; in e'@.
-- Mutually recursive functions are the fixpoint of a tuple.
-- @let f1 x1 = e1; f2 x2 = e2; in e'@ is equivalent to
-- @let rec fs = (\x1 -> e1, x2 -> e2); in let f1 = fst fs; f2 = snd fs; in e'@
data TmFun = TmFun TmVar TmVar Term

data Type
  = TySum Type Type
  | TyProd Type Type
  | TyArr Type Type
  | TyUnit
  | TyInt
  | TyVarOcc TyVar
  | TyAll TyVar Type

data TyVar
  = TyVar String

