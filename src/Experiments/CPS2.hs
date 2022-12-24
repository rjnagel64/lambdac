{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Experiments.CPS2 where

import Control.Monad.Reader

-- A variation of CPS where cps and cpsTail are merged, through use of an
-- auxiliary sum type 'Cont'

-- Reference: https://jtobin.io/transforming-to-cps
-- Reference: [Revisiting the CPS Transformation and its Implementation], François Pottier


type Name = String

data Expr
  = EVar Name
  | ELam Name Expr
  | EApp Expr Expr
  | ELet Name Expr Expr
  | EInl Expr
  | EInr Expr
  | ECase Expr (Name, Expr) (Name, Expr)
  | EInt Int
  deriving Show

data Type
  = TInt
  | TArr Type Type
  | TSum Type Type

data Term
  = KHalt KValue
  | KCallFun KValue KValue KValue
  | KCallCont KValue KValue
  | KCase KValue KValue KValue
  | KLet Name KValue Term
  deriving Show

data KValue
  = KVar Name
  | KFun Name Name Term
  | KCont Name Term
  | KInl KValue
  | KInr KValue
  | KInt Int
  deriving Show

data KType
  = KTInt
  | KTFun KType KCoType -- (a, b -> !) -> !
  | KTSum KType KType

data KCoType
  = KTCont KType -- (a) -> !

-- In my current IR, all functions and continuations are named, from CPS.IR
-- onwards.  This translation does not name functions or continuations. I need
-- some way to cope with that.
--
-- * I could have an immediate post-processing pass after CPS to clean this
--   up, but then I would have a mostly-redundant IR. (a nanopass to name
--   functions/conts in CPS)
--
-- * I could also make naming functions and continuations the responsibility
--   of CC. However, I currently plan to do most of my optimizations on CPS,
--   where it may be useful to have named fun/conts?

-- Realization: in the CPS translation algorithm, the continuation parameter
-- describes the context in which the expression is being translated.
--
-- * A MetaCont is an arbitrary evaluation context.
-- * An ObjCont (KVar "k") is a tail context.
-- * ObjCont (KLam ...) doesn't really make much sense? It should be MetaCont
--   to eliminate the redex when the continuation is applied.
--
-- I can also imagine an AppCont with an operand and an evaluation context /
-- Cont for the result. Hypothetically, this could be used to uncurry
-- applications. (The tricky part would be uncurrying the definitions, and then
-- ensuring that only that many values are taken from an AppCont)


-- Need at least Reader Int to implement fresh names.
fresh :: (Name -> M a) -> M a
fresh k = reader (\i -> runReader (k ("v" ++ show i)) (i+1))

type M a = Reader Int a


-- Γ |- c : ¬ t
-- In context Γ, the continuation 'c' accepts a value of type 't'.
data Cont
  -- If Γ |- k : (t) -> ! then Γ |- (ObjCont k) : ¬ t
  = ObjCont Name
  -- If f : _ -> _ then Γ |- (MetaCont f) : ¬ t
  | MetaCont (KValue -> M Term)
  -- Γ |- (HaltCont {t}) : ¬ t
  | HaltCont

-- apply : (Γ : Context) -> (v : KValue) ->
--         (_ : Γ |- c : ¬ t) ->
--         M ((Γ' : Context') * (e' : Term) * (Γ' |- e' OK))
apply :: Cont -> KValue -> M Term
apply (ObjCont k) v = pure (KCallCont (KVar k) v)
apply (MetaCont k) v = k v
apply HaltCont v = pure (KHalt v)

-- if Γ |- c : ¬ t
-- then Γ |- reify c : (t) -> !
--
-- reify : (Γ : Context) -> (c : Cont) ->
--         (_ : Γ |- c : ¬ t) ->
--         M ((Γ' : Context') * (v : KValue) * (Γ' |- v : (CPS-Ty[t]) -> !))
reify :: Cont -> M KValue
reify (ObjCont k) = pure (KVar k)
reify (MetaCont k) = fresh $ \x -> k (KVar x) >>= \e -> pure (KCont x e)
reify HaltCont = fresh $ \x -> pure $ KCont x (KHalt (KVar x))

-- cps : (Γ : Context) -> (e : Expr) -> (t : Type) -> (c : Cont) ->
--       (_ : Γ |- e : t) -> (_ : Γ |- c : ¬ t) ->
--       M ((Γ' : Context') * (e' : Term) * (Γ' |- e' OK))
cps :: Expr -> Cont -> M Term
cps (EVar x) c = apply c (KVar x)
cps (ELam x e) c = do
  v <- fresh $ \k -> KFun x k <$> cps e (ObjCont k)
  apply c v
cps (EApp e1 e2) c =
  cps e1 $ MetaCont $ \v1 ->
    cps e2 $ MetaCont $ \v2 ->
      KCallFun v1 v2 <$> reify c
cps (ELet x e1 e2) c =
  cps e1 $ MetaCont $ \v1 ->
    KLet x v1 <$> cps e2 c
cps (EInl e) c =
  cps e $ MetaCont $ \v -> apply c (KInl v)
cps (EInr e) c =
  cps e $ MetaCont $ \v -> apply c (KInr v)
cps (ECase e (x, e1) (y, e2)) c =
  cps e $ MetaCont $ \v ->
    fresh $ \k -> do
      k0 <- reify c -- continuation for the expression
      -- Use a let-binding so that the continuation is not duplicated by each
      -- branch.
      KLet k k0 <$> (do
        k1 <- KCont x <$> cps e1 (ObjCont k) -- left branch, cont x => [[e1]] k
        k2 <- KCont y <$> cps e2 (ObjCont k) -- right branch, cont y => [[e2]] k
        pure (KCase v k1 k2))
cps (EInt i) c = apply c (KInt i)


-- cpsMain : (e : Expr) -> (t : Type) -> {_ : ε |- e : t} -> ((e' : Term) * {_ : ε |- e' OK})
cpsMain :: Expr -> Term
cpsMain e = runReader (cps e HaltCont) 0

main :: IO ()
main = do
  print $ cpsMain (ELam "x" (EVar "x"))
  print $ cpsMain (EApp (ELam "x" (EVar "x")) (EVar "b"))
