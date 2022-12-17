
module Experiments.CPS2 where

import Control.Monad.Reader

-- A variation of CPS where cps and cpsTail are merged, through use of an
-- auxiliary sum type 'Cont'

-- Reference: https://jtobin.io/transforming-to-cps
-- Reference: [Revisiting the CPS Transformation and its Implementation], François Pottier


type Name = String

data Expr
  = EValue EValue
  | EApp Expr Expr
  | ELet Name Expr Expr
data EValue
  = EVar Name
  | ELam Name Expr

data Term
  = KValue KValue
  | KCall Term KValue
  | KLet Name KValue Term

data KValue
  = KVar Name
  -- I don't really like how functions are treated as atoms.
  -- This can lead to redexes like (\x. x) 17 being left in.
  -- ==> stratify a bit, re-introduce let-bindings for functions?
  -- ==> reify MetaCont needs work, to hoist the contdef out of the jump
  -- ==> (Hang on, a let-bound function still involves a redex, it's just hidden)
  --
  -- I guess what I want to say is that having a lambda is okay in argument
  -- position, but I don't really want to have a lambda in function position,
  -- because that's a redex that should be eliminated, right?
  --
  -- Or maybe, redexes in the source language should still be redexes in the
  -- target language? So it's actually fine?
  -- CPS should not introduce extra redexes, but redexes in the source language
  -- are fine.
  --
  -- Also, 'letfun f x k = ... in f 17 halt' is a redex, just disguised slightly,
  -- so my original doubt was incoherent.
  --
  -- I guess what I really want to say is that in my current IR, all functions
  -- and continuations are named, from CPS.IR onwards.
  --
  -- This translation does not name functions or continuations. I need some way
  -- to cope with that.
  -- * I could have an immediate post-processing pass after CPS to clean this
  -- up, but then I would have a mostly-redundant IR. (a nanopass to name
  -- functions/conts in CPS)
  --
  -- * I could also make naming functions and continuations the responsibility
  -- of CC. However, I currently plan to do most of my optimizations on CPS,
  -- where it may be useful to have named fun/conts?
  | KLam Name Term



-- Need at least Reader Int to implement fresh names.
fresh :: (Name -> M a) -> M a
fresh k = reader (\i -> runReader (k ("v" ++ show i)) (i+1))

type M a = Reader Int a


data Cont
  -- Hmm. Does it make sense to have 'ObjCont (KLam x e)', or could I restrict
  -- this to 'ObjCont Name'?
  = ObjCont KValue
  | MetaCont (KValue -> M Term)

apply :: Cont -> KValue -> M Term
apply (ObjCont k) v = pure (KCall (KValue k) v)
apply (MetaCont k) v = k v

reify :: Cont -> M KValue
reify (ObjCont k) = pure k
reify (MetaCont k) = fresh $ \x -> KLam x <$> k (KVar x)

cpsValue :: EValue -> M KValue
cpsValue (EVar x) = pure (KVar x)
cpsValue (ELam x e) = fresh $ \y -> KLam x . KValue . KLam y <$> cps e (ObjCont (KVar y))

cps :: Expr -> Cont -> M Term
cps (EValue v) c = apply c =<< cpsValue v
cps (EApp e1 e2) c =
  cps e1 $ MetaCont $ \v1 ->
    cps e2 $ MetaCont $ \v2 ->
      KCall (KCall (KValue v1) v2) <$> reify c
cps (ELet x e1 e2) c =
  cps e1 $ MetaCont $ \v1 ->
    KLet x v1 <$> cps e2 c


cpsMain :: Expr -> Term
cpsMain e = runReader (cps e (ObjCont (KVar "halt"))) 0 -- just return the CPS'ed term.
