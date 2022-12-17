
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
  deriving Show

data Term
  = KHalt KValue
  | KCallFun KValue KValue KValue
  | KCallCont KValue KValue
  | KLet Name KValue Term
  deriving Show

data KValue
  = KVar Name
  | KFun Name Name Term
  | KCont Name Term
  deriving Show

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


data Cont
  = ObjCont Name
  | MetaCont (KValue -> M Term)
  | HaltCont

apply :: Cont -> KValue -> M Term
apply (ObjCont k) v = pure (KCallCont (KVar k) v)
apply (MetaCont k) v = k v
apply HaltCont v = pure (KHalt v)

reify :: Cont -> M KValue
reify (ObjCont k) = pure (KVar k)
reify (MetaCont k) = fresh $ \x -> KCont x <$> k (KVar x)
reify HaltCont = fresh $ \x -> pure $ KCont x (KHalt (KVar x))

cps :: Expr -> Cont -> M Term
cps (EVar x) c = apply c (KVar x)
cps (ELam x e) c = apply c =<< (fresh $ \y -> KFun x y <$> cps e (ObjCont y))
cps (EApp e1 e2) c =
  cps e1 $ MetaCont $ \v1 ->
    cps e2 $ MetaCont $ \v2 ->
      KCallFun v1 v2 <$> reify c
cps (ELet x e1 e2) c =
  cps e1 $ MetaCont $ \v1 ->
    KLet x v1 <$> cps e2 c


cpsMain :: Expr -> Term
cpsMain e = runReader (cps e HaltCont) 0 -- just return the CPS'ed term.

main :: IO ()
main = do
  print $ cpsMain (ELam "x" (EVar "x"))
  print $ cpsMain (EApp (ELam "x" (EVar "x")) (EVar "b"))
