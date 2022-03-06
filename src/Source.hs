
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
  -- case e of inl (x : t1) -> e1; inr (y : t2) -> e2
  -- TODO: Add return-type annotation on case-expressions?
  | TmCase Term (TmVar, Type, Term) (TmVar, Type, Term)
  -- inl e
  | TmInl Term
  -- inr e
  | TmInr Term
  -- \ (x:t) -> e
  | TmLam TmVar Type Term
  -- e1 e2
  | TmApp Term Term
  -- (e1, e2)
  | TmPair Term Term
  -- fst e
  | TmFst Term
  -- snd e
  | TmSnd Term
  -- let x:t = e1 in e2
  | TmLet TmVar Type Term Term
  -- let rec fs+ in e
  | TmRecFun [TmFun] Term
  -- ()
  | TmNil
  -- 17
  | TmInt Int
  -- e1 + e2
  | TmAdd Term Term
  -- e1 - e2
  | TmSub Term Term
  -- e1 * e2
  | TmMul Term Term
  -- iszero e
  | TmIsZero Term


-- @f (x : t) := e@, used for recursion.
-- I'm not really satisfied with this. How does a 'TmFun' interact with polymorphism?
-- How does it deal with multiple parameters? (i.e., if I allow 'TmFun' to have
-- multiple parameters, are unsaturated applications permitted?)
-- What do multiple-argument functions look like after CPS?
--
-- @let fun f x = e; in e'@ is basically @let rec f = \x -> e; in e'@.
-- Mutually recursive functions are the fixpoint of a tuple.
-- @let f1 x1 = e1; f2 x2 = e2; in e'@ is equivalent to
-- @let rec fs = (\x1 -> e1, x2 -> e2); in let f1 = fst fs; f2 = snd fs; in e'@
-- I think that this encoding is inefficient, though. (environment contains
-- tuple instead of pointers to recursive occurrences directly?)
--
-- I think I should add a @let rec@ construct, such as
-- @let rec x1 = e1; x2 = e2; ...; in e'@.
-- This is desirable, because I can make mutually recursive, many-argument,
-- polymorphic functions easily?
-- This level of generality is not desirable, because I have strict evaluation
-- and cyclic values require laziness to not diverge.
-- ... Can I do patching like for closures?
-- value *x1 = alloc_pair(1, NULL);
-- value *x2 = alloc_pair(2, NULL);
-- x1->snd = x2;
-- x2->snd = x1;
--
-- Is there a difference between partially-applied occurrences within
-- definition versus partially-applied occurrences within body?
data TmFun = TmFun TmVar TmVar Type Term

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

