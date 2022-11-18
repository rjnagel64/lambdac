{-# LANGUAGE StandaloneDeriving, DerivingStrategies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase #-}

module Experiments.Inference where

import Control.Monad.State
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

-- It should be straightforward to derive rules for products and sums
-- (via scott-encoding?)
-- (or maybe just directly.)


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
open (TyUVar bb) aa a' = if bb == aa then TyEVar a' else TyUVar bb
open (TyEVar b') _ _ = TyEVar b'
open TyUnit _ _ = TyUnit
open (TyArr a b) aa a' = TyArr (open a aa a') (open b aa a')
open (TyForall bb a) aa a' = if bb == aa then TyForall bb a else TyForall bb (open a aa a')

-- | Monotypes are types that do not include 'TyForall' anywhere in their
-- structure.
data Mono
  = MonoUnit
  | MonoUVar UVar
  | MonoEVar EVar
  | MonoArr Mono Mono

isMonoType :: Type -> Maybe Mono
isMonoType (TyForall _ _) = Nothing
isMonoType (TyUVar aa) = Just (MonoUVar aa)
isMonoType (TyEVar a') = Just (MonoEVar a')
isMonoType TyUnit = Just MonoUnit
isMonoType (TyArr t s) = MonoArr <$> isMonoType t <*> isMonoType s

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
substCtx _ TyUnit = TyUnit
substCtx _ (TyUVar aa) = TyUVar aa
substCtx g (TyArr a b) = TyArr (substCtx g a) (substCtx g b)
substCtx g (TyEVar a') = case focus a' g of
  Nothing -> error "evar not in substitution"
  Just (_, FocusUnsolved _, _) -> TyEVar a'
  Just (_, FocusSolved _ t, _) -> substCtx g (fromMono t)
-- This is surprising, that no scope management needs to be done.
-- I guess it's because the substitution is only on 'EVar's, and there are no
-- 'EVar' binders to worry about.
substCtx g (TyForall aa a) = TyForall aa (substCtx g a)

-- | Discard the tail of a context, up to and including the first entry that
-- satisfies a predicate.
discardTail :: Context -> (Entry -> Bool) -> Context
discardTail Empty _ = Empty
discardTail (g :>: e) p = if p e then g else discardTail g p

discardVar :: Context -> Var -> Context
discardVar g x = discardTail g $ \case
  EntryVar y _ -> x == y
  _ -> False

discardUVar :: Context -> UVar -> Context
discardUVar g aa = discardTail g $ \case
  EntryUVar bb -> aa == bb
  _ -> False

discardMarker :: Context -> EVar -> Context
discardMarker g a' = discardTail g $ \case
  EntryMarker b' -> a' == b'
  _ -> False

data FocusItem = FocusUnsolved EVar | FocusSolved EVar Mono
type Focus = (Context, FocusItem, Context)

-- | Decompose a context into a left context, a focused 'EVar', and a right
-- context.
-- 
-- Returns 'Nothing' if @a'@ is not present in the context.
focus :: EVar -> Context -> Maybe Focus
focus _ Empty = Nothing
focus a' (g :>: EntryEVar b')
  | a' == b' = Just (g, FocusUnsolved b', Empty)
focus a' (g :>: EntrySolved b' t)
  | a' == b' = Just (g, FocusSolved b' t, Empty)
focus a' (g :>: e) =
  (\ (gl, x, gr) -> (gl, x, gr :>: e)) <$> focus a' g

unfocus :: Focus -> Context
unfocus (gl, FocusUnsolved a', gr) = gl :>: EntryEVar a' >:> gr
unfocus (gl, FocusSolved a' t, gr) = gl :>: EntrySolved a' t >:> gr

splice :: Focus -> Context -> Context
splice (gl, _, gr) h = gl >:> h >:> gr

-- | Turn @Γ[α']@, @α' = τ@ into @Γ[α := τ]@.
solve :: EVar -> Mono -> Context -> Maybe Context
solve a' t g = case focus a' g of
  Nothing -> Nothing
  Just (_, FocusSolved _ _, _) -> error "duplicate solve"
  Just (gl, FocusUnsolved b', gr) -> Just (unfocus (gl, FocusSolved b' t, gr))

-- | Turn @Γ[α'][β']@ into @Γ[α'][β' = α']@
reach :: Context -> EVar -> EVar -> Maybe Context
reach g a' b' = case focus b' g of
  Nothing -> Nothing
  Just (_, FocusSolved _ _, _) -> error "reach: duplicate solve"
  Just (g', FocusUnsolved _, gr) -> Just (g' :>: EntrySolved b' (MonoEVar a') >:> gr)


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
occurs _ TyUnit = False
occurs _ (TyUVar _) = False -- EVar cannot be UVar
occurs a' (TyArr a b) = occurs a' a || occurs a' b
occurs a' (TyForall _ a) = occurs a' a -- bound variable is a UVar, and cannot bind/shadow a'.

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
  pure (a2', a1', g')

lookupVar :: Context -> Var -> M Type
lookupVar Empty _ = throwError "variable not in scope"
lookupVar (g :>: EntryVar y t) x =
  if x == y then
    pure t
  else
    lookupVar g x
lookupVar (g :>: _) x = lookupVar g x

lookupEVar :: Context -> EVar -> M (Maybe Mono)
lookupEVar Empty _ = throwError "existential variable not in scope"
lookupEVar (_ :>: EntryEVar b') a'
  | a' == b' = pure Nothing
lookupEVar (_ :>: EntrySolved b' t) a' 
  | a' == b' = pure (Just t)
lookupEVar (g :>: _) a' = lookupEVar g a'


subtype :: Context -> Type -> Type -> M Context
-- Reflexive cases
subtype g (TyEVar a') (TyEVar b') | a' == b' = pure g
subtype g (TyUVar aa) (TyUVar bb)
  | aa == bb = pure g
  | otherwise = throwError "distinct rigid type variables cannot unify"
subtype g TyUnit TyUnit = pure g
-- Arrow types
subtype g (TyArr a1 a2) (TyArr b1 b2) = do
  h <- subtype g b1 a1
  d <- subtype h (substCtx h a2) (substCtx h b2)
  pure d
-- Universal quantification
subtype g a (TyForall aa b) = do
  dh <- subtype (g :>: EntryUVar aa) a b
  let d = discardUVar dh aa
  pure d
subtype g (TyForall aa a) b = do
  a' <- newEVar
  dh <- subtype (g :>: EntryMarker a') (open a aa a') b
  let d = discardMarker dh a'
  pure d
-- instantiation
subtype g (TyEVar a') a = do
  occursM a' a
  instantiateL g a' a
subtype g a (TyEVar a') = do
  occursM a' a
  instantiateR g a a'
-- error cases
subtype _ TyUnit (TyUVar _) = throwError "'unit' is not a subtype of rigid type variable"
subtype _ TyUnit (TyArr _ _) = throwError "'unit' is not a subtype of function type"
subtype _ (TyUVar _) TyUnit = throwError "rigid type variable is not a subtype of 'unit'"
subtype _ (TyUVar _) (TyArr _ _) = throwError "rigid type variable is not a subtype of function type"
subtype _ (TyArr _ _) TyUnit = throwError "function type is not a subtype of 'unit'"
subtype _ (TyArr _ _) (TyUVar _) = throwError "function type is not a subtype of rigid type variable"


instantiateL :: Context -> EVar -> Type -> M Context
instantiateL g a' (TyEVar b') = do
  g' <- maybe (throwError "reach failed") pure (reach g a' b')
  pure g'
instantiateL g a' (TyForall bb b) = do
  dh <- instantiateL (g :>: EntryUVar bb) a' b
  let d = discardUVar dh bb
  pure d
instantiateL g a' (TyArr a1 a2) = do
  (a2', a1', g') <- articulate g a'
  h <- instantiateR g' a1 a1'
  d <- instantiateL h a2' (substCtx h a2)
  pure d
instantiateL g a' a = case isMonoType a of
  Just t -> do
    wfMono g t
    g' <- maybe (throwError "solve failed") pure (solve a' t g)
    pure g'
  Nothing -> error "unreachable: non-monotypes and monotypes both covered"

instantiateR :: Context -> Type -> EVar -> M Context
instantiateR g (TyEVar b') a' = do
  g' <- maybe (throwError "reach failed") pure (reach g a' b')
  pure g'
instantiateR g (TyForall bb b) a' = do
  b' <- newEVar
  dh <- instantiateR (g :>: EntryMarker b' :>: EntryEVar b') (open b bb b') a'
  let d = discardMarker dh b'
  pure d
instantiateR g (TyArr a1 a2) a' = do
  (a2', a1', g') <- articulate g a'
  h <- instantiateL g' a1' a1
  d <- instantiateR h (substCtx h a2) a2'
  pure d
instantiateR g a a' = case isMonoType a of
  Just t -> do
    wfMono g t
    g' <- maybe (throwError "solve failed") pure (solve a' t g)
    pure g'
  Nothing -> error "unreachable: non-monotypes and monotypes both covered"


check :: Context -> Term -> Type -> M Context
check g e (TyForall aa a) = do
  dh <- check (g :>: EntryUVar aa) e a
  let d = discardUVar dh aa
  pure d
check g TmUnit TyUnit = pure g
check g (TmLam x e) (TyArr a b) = do
  dh <- check (g :>: EntryVar x a) e b
  let d = discardVar dh x
  pure d
check g e b = do
  (a, h) <- infer g e
  d <- subtype h (substCtx h a) (substCtx h b)
  pure d

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
app _ TyUnit _ = throwError "'unit' cannot have argument applied to it"
app _ (TyUVar _) _ = throwError "rigid type variable cannot have argument applied to it"


-- | Assert that a monotype is well-formed w.r.t. a context.
wfMono :: Context -> Mono -> M ()
wfMono g t = pure ()


-- Random idea: algorithmic inference as an arrow. I'm not really sure what
-- that would look like, though.
--
-- type Arr a b = (Context, a) -> E (Context, b) ? (thread context through)
-- type Arr a b = a -> E b ? (Just kliesli)


inferProgram :: Term -> Either String (Type, Context)
inferProgram e = runExcept $ flip evalStateT 0 $ runM $ infer Empty e

-- Debug purposes, mostly.
main :: IO ()
main = do
  -- \x -> \f -> f x
  -- - : forall a. forall b. a -> (a -> b) -> b
  -- (No generalization done, though)
  let e :: Term; e = (TmLam (Var "x") (TmLam (Var "f") (TmApp (TmVar (Var "f")) (TmVar (Var "x")))))
  case inferProgram e of
    Left err -> do
      putStrLn "error:"
      print err
    Right (t, d) -> do
      putStrLn "ok:"
      putStrLn $ pprintContext d ++ " |- " ++ pprintType 0 t
      putStrLn $ pprintType 0 (substCtx d t)

pprintContext :: Context -> String
pprintContext Empty = "."
pprintContext (g :>: e) = pprintContext g ++ ", " ++ pprintEntry e

pprintEntry :: Entry -> String
pprintEntry (EntryEVar a') = show a'
pprintEntry (EntryUVar aa) = show aa
pprintEntry (EntrySolved a' t) = show a' ++ " = " ++ pprintMono 0 t
pprintEntry (EntryMarker a') = "|> " ++ show a'
pprintEntry (EntryVar x a) = show x ++ " : " ++ pprintType 0 a

pprintType :: Int -> Type -> String
pprintType p TyUnit = "unit"
pprintType p (TyArr a b) = parensIf (p > 5) $ pprintType 6 a ++ " -> " ++ pprintType 5 b
pprintType p (TyForall aa a) = parensIf (p > 0) $ "forall " ++ show aa ++ ". " ++ pprintType 0 a
pprintType p (TyUVar aa) = show aa
pprintType p (TyEVar a') = show a'

pprintMono :: Int -> Mono -> String
pprintMono p MonoUnit = "unit"
pprintMono p (MonoArr a b) = parensIf (p > 5) $ pprintMono 6 a ++ " -> " ++ pprintMono 5 b
pprintMono p (MonoUVar aa) = show aa
pprintMono p (MonoEVar a') = show a'

instance Show Var where
  show (Var x) = x

instance Show UVar where
  show (UVar aa) = aa

instance Show EVar where
  show (EVar i) = "#" ++ show i

parensIf :: Bool -> String -> String
parensIf False s = s
parensIf True s = "(" ++ s ++ ")"
