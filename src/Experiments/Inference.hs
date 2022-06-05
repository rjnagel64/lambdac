{-# LANGUAGE StandaloneDeriving, DerivingStrategies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Experiments.Inference where

import Data.Maybe

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

-- Complete and Easy Bidirectional Type Checking for Higher-Rank Polymorphism
--
-- It looks surprisingly straightforward, and goes out of its way to be
-- algorithmic.
--
-- It's just a type inference/checking algorithm, but I'm pretty sure I can
-- tweak it into an elaborator that outputs fully-annotated System F (Source)
--
-- It supports rank-N types, while only needing annotations on polymorphic let
-- bindings, but it does not support impredicative instantiations (type
-- variables only get instantiated with monotypes)
--
-- so 'id id' is not valid, I think. Or at least needs a type annotation.
--
-- I wonder how it interacts with explicit type applications and/or scoped type
-- variables


-- Elaboration to System F looks pretty straightforward.

-- TODO: Derive rules for products and sums


data Var = Var String
  deriving Eq

data Term
  = TmVar Var
  | TmUnit
  | TmLam Var Term
  | TmApp Term Term
  | TmAnn Term Type

-- Universal variables, used by forall quantifiers
data UVar = UVar String
  deriving Eq
-- Existential variables, used during unification
data EVar = EVar Int
  deriving Eq

data Type
  = TyUnit
  | TyUVar UVar
  | TyEVar EVar
  | TyForall UVar Type
  | TyArr Type Type

-- | Replace the uvar @α@ with the evar @α'@.
-- Used when removing the top-level forall of a type
open :: Type -> UVar -> EVar -> Type
open TyUnit aa a' = TyUnit

-- | Monotypes are types that do not include 'TyForall' anywhere in their
-- structure.
data Mono
  = MonoUnit
  | MonoUVar UVar
  | MonoEVar EVar
  | MonoArr Mono Mono

isMonoType :: Type -> Maybe Mono
isMonoType (TyForall _ _) = Nothing
isMonoType (TyArr t s) = MonoArr <$> isMonoType t <*> isMonoType s
isMonoType TyUnit = pure MonoUnit

fromMono :: Mono -> Type
fromMono MonoUnit = TyUnit
fromMono (MonoUVar aa) = TyUVar aa
fromMono (MonoEVar a') = TyEVar a'
fromMono (MonoArr a b) = TyArr (fromMono a) (fromMono b)

-- | Contexts are ordered sequences of annotations and bindings
data Context
  = Empty
  | Context :>: Entry

data Entry
  = EntryVar Var Type
  | EntryUVar UVar
  | EntryEVar EVar
  | EntrySolved EVar Mono
  | EntryMarker EVar

-- | Context concatenation
(>:>) :: Context -> Context -> Context
g >:> Empty = g
g >:> (g' :>: e) = (g >:> g') :>: e

-- | Complete contexts are ones where all existential variables are CtxSolved.
-- (Could use a GADT to rule out EntryEVar, I guess.)
type Complete = Context


-- | Apply a context as a substitution on 'EVar's.
substCtx :: Context -> Type -> Type
substCtx g TyUnit = TyUnit
substCtx g (TyUVar aa) = TyUVar aa
substCtx g (TyArr a b) = TyArr (substCtx g a) (substCtx g b)
substCtx g (TyEVar a') = case focus a' g of
  Nothing -> error "evar not in substitution"
  Just (_, EntryEVar _, _) -> error "unsolved evar in substitution"
  Just (_, EntrySolved _ t, _) -> substCtx g (fromMono t)
-- This is surprising, that no scope management needs to be done.
-- I guess it's because the substitution is only on 'EVar's, and there are no
-- 'EVar' binders to worry about.
substCtx g (TyForall aa a) = TyForall aa (substCtx g a)

-- | Given @Δ, β, Δ'@, return @Δ@.
discardTail :: Context -> (Entry -> Bool) -> Context
discardTail Empty p = Empty
discardTail (g :>: e) p = if p e then g else discardTail g p

discardVar g x = discardTail g $ \case
  EntryVar y _ -> x == y
  _ -> False
discardUVar g aa = discardTail g $ \case
  EntryUVar bb -> aa == bb
  _ -> False

type Focus = (Context, Entry, Context)

-- | Decompose a context into a left context, a focused item, and a right
-- context.
-- 
-- Returns 'Nothing' if @a'@ is not present in the context.
focus :: EVar -> Context -> Maybe Focus
focus a' Empty = Nothing
focus a' (g :>: EntryEVar b') =
  if a' == b' then
    Just (g, EntryEVar b', Empty)
  else
    (\ (g, x, g') -> (g, x, g' :>: EntryEVar b')) <$> focus a' g
focus a' (g :>: EntrySolved b' t) =
  if a' == b' then
    Just (g, EntrySolved b' t, Empty)
  else
    (\ (g, x, g') -> (g, x, g' :>: EntrySolved b' t)) <$> focus a' g

splice :: Focus -> Context -> Context
splice (g, _, g') h = g >:> h >:> g'

-- | Turn @Γ[α']@, @α' = τ@ into @Γ[α := τ]@.
solve :: EVar -> Mono -> Context -> Maybe Context
solve a' t Empty = Nothing -- Should not occur, if well-scoped.
solve a' t (g :>: EntryEVar b') =
  if a' == b' then
    pure (g :>: EntrySolved a' t)
  else
    fmap (:>: EntryEVar b') (solve a' t g)
solve a' t (g :>: EntrySolved b' s) =
  if a' == b' then
    Nothing -- duplicate solve
  else
    fmap (:>: EntrySolved b' s) (solve a' t g)

-- | Turn @Γ[α'][β']@ into @Γ[α'][β' = α']@
reach :: Context -> EVar -> EVar -> Maybe Context
reach g a' b' = case focus b' g of
  Nothing -> Nothing
  Just (_, EntrySolved _ _, _) -> Nothing
  Just (g', EntryEVar _, gr) -> Just (g' :>: EntrySolved b' (MonoEVar a') >:> gr)


newtype M a = M { runM :: StateT Int (Except String) a }

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadState Int M
deriving newtype instance MonadError String M

newEVar :: M EVar
newEVar = do
  i <- get
  modify' (+1)
  pure (EVar i)

-- | Perform the occurs check: test whether @a'@ is a free variable in @a@.
-- This is necessary to avoid infinite substitutions, such as @a' ~ a' -> Unit@.
occurs :: EVar -> Type -> Bool
occurs a' (TyEVar b') = a' == b'
occurs a' TyUnit = False
occurs a' (TyArr a b) = occurs a' a || occurs a' b
occurs a' (TyForall bb a) = occurs a' a -- bb is a UVar, and cannot bind a'.

occursM :: EVar -> Type -> M ()
occursM a' a = when (occurs a' a) $ throwError "occurs check failed"

-- | "Articulate" @Γ[α']@ by expanding an arrow type: @Γ[α2', α1', α' = α1' -> α2']@.
-- I may need to generalize this to deal with other type constructors.
articulate :: Context -> EVar -> M (EVar, EVar, Context)
articulate g a' = do
  a1' <- newEVar
  a2' <- newEVar
  f <- maybe (throwError "focus failed") pure (focus a' g)
  let ty = (MonoArr (MonoEVar a1') (MonoEVar a2'))
  let h = (Empty :>: EntryEVar a2' :>: EntryEVar a1' :>: EntrySolved a' ty)
  let g' = splice f h
  pure (a1', a2', g')

lookupVar :: Context -> Var -> M Type
lookupVar Empty x = throwError "variable not in scope"
lookupVar (g :>: EntryVar y t) x =
  if x == y then
    pure t
  else
    lookupVar g x
lookupVar (g :>: _) x = lookupVar g x

lookupEVar :: Context -> EVar -> M (Maybe Mono)
lookupEVar Empty a' = throwError "existential variable not in scope"
lookupEVar (g :>: EntryEVar b') a' =
  if a' == b' then
    pure Nothing
  else
    lookupEVar g a'
lookupEVar (g :>: EntrySolved b' t) a' =
  if a' == b' then
    pure (Just t)
  else
    lookupEVar g a'

subtype :: Context -> Type -> Type -> M Context
subtype g TyUnit TyUnit = pure g
subtype _ TyUnit _ = throwError "'unit' is not a subtype of $other"
subtype g (TyArr a1 a2) (TyArr b1 b2) = do
  h <- subtype g b1 a1
  d <- subtype h (substCtx h a2) (substCtx h b2)
  pure d
-- TODO: Reflexive case, a' <: a', before delegating to instantiate[LR]
subtype g (TyEVar a') a = do
  occursM a' a
  instantiateL g a' a
subtype g a (TyEVar a') = do
  occursM a' a
  instantiateR g a a'
subtype g a (TyForall aa b) = do
  dh <- subtype (g :>: EntryUVar aa) a b
  let d = discardUVar dh aa
  pure d

instantiateL :: Context -> EVar -> Type -> M Context
-- Annoying: the pattern-match coverage check isn't smart enough here:
-- Subsequent branches will only be taken for polytypes, but it doesn't
-- recognize that fact.
--
-- Find a way to appease the coverage check, I guess. Preferably without
-- duplicating the 'solve' logic in every case.
instantiateL g a' a | Just t <- isMonoType a = do
  wfMono g t
  g' <- maybe (throwError "solve failed") pure (solve a' t g)
  pure g'
instantiateL g a' (TyArr a1 a2) = do
  (a2', a1', g') <- articulate g a'
  h <- instantiateR g' a1 a1'
  d <- instantiateL h a2' (substCtx h a2)
  pure d
instantiateL g a' (TyEVar b') = do
  g' <- maybe (throwError "reach failed") pure (reach g a' b')
  pure g'

instantiateR :: Context -> Type -> EVar -> M Context
instantiateR g a a' | Just t <- isMonoType a = do
  wfMono g t
  g' <- maybe (throwError "solve failed") pure (solve a' t g)
  pure g'
instantiateR g (TyArr a1 a2) a' = do
  (a2', a1', g') <- articulate g a'
  h <- instantiateL g' a1' a1
  d <- instantiateR h (substCtx h a2) a2'
  pure d
instantiateR g (TyEVar b') a' = do
  g' <- maybe (throwError "reach failed") pure (reach g a' b')
  pure g'


check :: Context -> Term -> Type -> M Context
check g (TmLam x e) (TyArr a b) = do
  dh <- check (g :>: EntryVar x a) e b
  let d = discardVar dh x
  pure d
check g TmUnit TyUnit = pure g
check g e (TyForall aa a) = do
  dh <- check (g :>: EntryUVar aa) e a
  let d = discardUVar dh aa
  pure d
-- check g e b = do
--   (a, h) <- infer g e
--   d <- subtype h (substCtx h a) (substCtx h b)
--   pure d

infer :: Context -> Term -> M (Type, Context)
infer g (TmVar x) = do
  a <- lookupVar g x
  pure (a, g)
infer g (TmAnn e a) = do
  d <- check g e a
  pure (a, d)
infer g TmUnit = pure (TyUnit, g)
infer g (TmApp e1 e2) = do
  (a, h) <- infer g e1
  (c, d) <- app h (substCtx h a) e2
  pure (c, d)
infer g (TmLam x e) = do
  a' <- newEVar
  b' <- newEVar
  dh <- check (g :>: EntryEVar a' :>: EntryEVar b' :>: EntryVar x (TyEVar a')) e (TyEVar b')
  let d = discardVar dh x
  pure (TyArr (TyEVar a') (TyEVar b'), d)

app :: Context -> Type -> Term -> M (Type, Context)
app g (TyArr a c) e = do
  d <- check g e a
  pure (c, d)
app g (TyForall aa a) e = do
  a' <- newEVar
  (c, d) <- app (g :>: EntryEVar a') (open a aa a') e
  pure (c, d)
app g (TyEVar a') e = do
  (a2', a1', g') <- articulate g a'
  d <- check g' e (TyEVar a1')
  pure (TyEVar a2', d)
app g TyUnit e = throwError "'unit' cannot have argument applied to it"


-- | Assert that a monotype is well-formed w.r.t. a context.
wfMono :: Context -> Mono -> M ()
wfMono g t = pure ()


-- Random idea: algorithmic inference as an arrow. I'm not really sure what
-- that would look like, though.
--
-- type Arr a b = (Context, a) -> E (Context, b) ? (thread context through)
-- type Arr a b = a -> E b ? (Just kliesli)
