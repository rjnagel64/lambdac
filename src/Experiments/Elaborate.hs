{-# LANGUAGE StandaloneDeriving, DerivingStrategies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase #-}
-- {-# OPTIONS_GHC -Wall #-}

module Experiments.Elaborate where

import Control.Monad.State
import Control.Monad.Except

-- Try to adapt Experiments.Inference to produce an elaborated term as output.

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
--
-- The big question, I guess, is this:
-- do fst/snd and case..of count as eliminators for spines?
-- Probably.
-- (If you use 'either' for case..of and encode tuples as '(x, y) === \f -> f x
-- y', then yeah, using those constructs means function application, which
-- creates a spine.)

-- The other big question: higher-kinded types. These rules only use kind *
-- (i.e., need rules for tyapp, tycon, etc.)


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


data Term'
  = TmVar' Var
  | TmUnit'
  | TmLam' Var Type Term'
  | TmApp' Term' Term'
  | TmTLam' UVar Term'
  | TmTApp' Term' Type

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


-- Evidence term for reflexive coercion
reflCo :: Type -> Term'
reflCo a = TmLam' (Var "x") a (TmVar' (Var "x"))

-- Construct a coercion between two function types.
-- Contravariant input, covariant output.
-- General form: in : b1 -> a1; out : a2 -> b2.
-- λ (f : a1 -> a2). λx. out (f (in x))
funCo :: (Type, Type) -> (Type, Type) -> Coercion -> Coercion -> Coercion
-- both are reflexive, erased. this coercion is then λf.λx.f x
-- This eta-reduces to identity, which is reflCo.
funCo (a1, a2) (b1, b2) (ReflCo t1) (ReflCo t2) = ReflCo (TyArr b1 b2)
-- Otherwise, we need at least one of the casts.
funCo (a1, a2) (b1, b2) f1 f2 = Coercion co
  where
    co = TmLam' fv (TyArr a1 a2) (TmLam' xv b1 body)
    body = appCo f1 (TmApp' (TmVar' fv) (appCo f2 (TmVar' xv)))
    -- body = TmApp' f1 (TmApp' (TmVar' fv) (TmApp' f2 (TmVar' xv)))
    fv = Var "f"
    xv = Var "x"

data Coercion
  = ReflCo Type
  | Coercion Term'

appCo :: Coercion -> Term' -> Term'
-- reflexive coercions are identity, and can be eliminated at compile time.
appCo (ReflCo _) e' = e'
appCo (Coercion f) e' = TmApp' f e'

-- '(d, f) <- subtype g a b' shows that in context 'g', 'a' is a subtype of
-- 'b'.
-- It produces an output context 'd', and a coercion term 'f' with type
-- 'a -> b'.
--
-- Hmmmmm. At the end of the day, every coercion is reflexive. Coercions are
-- therefore redundant. And very messy. They bloat the output.
-- I should try to avoid emitting them, where possible.
-- (Okay, maybe there's something about polymorphic subtyping that is
-- not-quite-identity, but still.)
subtype :: Context -> Type -> Type -> M (Context, Coercion)
-- Reflexive cases
subtype g (TyEVar a') (TyEVar b')
  | a' == b' = pure (g, ReflCo (TyEVar a'))
  -- inequal case is handled below, under "instantiation"
subtype g (TyUVar aa) (TyUVar bb)
  | aa == bb = pure (g, ReflCo (TyUVar aa))
  | otherwise = throwError "distinct rigid type variables cannot unify"
subtype g TyUnit TyUnit = pure (g, ReflCo TyUnit)
-- Arrow types
subtype g (TyArr a1 a2) (TyArr b1 b2) = do
  (h, f1) <- subtype g b1 a1
  (d, f2) <- subtype h (substCtx h a2) (substCtx h b2)
  pure (d, funCo (a1, a2) (b1, b2) f1 f2)
-- Universal quantification
subtype g a (TyForall aa b) = do
  (dh, f) <- subtype (g :>: EntryUVar aa) a b
  let d = discardUVar dh aa
  pure (d, f) -- might need TmTLam' here?
subtype g (TyForall aa a) b = do
  a' <- newEVar
  (dh, f) <- subtype (g :>: EntryMarker a') (open a aa a') b
  let d = discardMarker dh a'
  pure (d, f) -- might need a TmTApp' here?
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


-- "instantiateL g a' b" shows that a' is a subtype of b.
instantiateL :: Context -> EVar -> Type -> M (Context, Coercion)
instantiateL g a' (TyEVar b') = do
  g' <- maybe (throwError "reach failed") pure (reach g a' b')
  pure (g', ReflCo (TyEVar b'))
instantiateL g a' (TyForall bb b) = do
  (dh, f) <- instantiateL (g :>: EntryUVar bb) a' b
  let d = discardUVar dh bb
  pure (d, Coercion (TmTLam' bb (TmLam' (Var "x") (TyEVar a') (appCo f (TmVar' (Var "x"))))))
instantiateL g a' (TyArr a1 a2) = do
  (a2', a1', g') <- articulate g a'
  (h, f1) <- instantiateR g' a1 a1'
  (d, f2) <- instantiateL h a2' (substCtx h a2)
  pure (d, funCo (TyEVar a1', TyEVar a2') (a1, a2) f1 f2)
instantiateL g a' a = case isMonoType a of
  Just t -> do
    wfMono g t
    g' <- maybe (throwError "solve failed") pure (solve a' t g)
    pure (g', ReflCo (fromMono t)) -- In g', a' := t. coercion is therfore reflexive
  Nothing -> error "unreachable: non-monotypes and monotypes both covered"

-- "instantiateR g b a'" shows that b is a subtype of a'
instantiateR :: Context -> Type -> EVar -> M (Context, Coercion)
instantiateR g (TyEVar b') a' = do
  g' <- maybe (throwError "reach failed") pure (reach g a' b')
  pure (g', ReflCo (TyEVar b'))
instantiateR g (TyForall bb b) a' = do
  b' <- newEVar
  (dh, f) <- instantiateR (g :>: EntryMarker b' :>: EntryEVar b') (open b bb b') a'
  let d = discardMarker dh b'
  let co = Coercion (TmLam' (Var "f") (TyForall bb b) (appCo f (TmTApp' (TmVar' (Var "f")) (TyEVar b'))))
  pure (d, co)
instantiateR g (TyArr a1 a2) a' = do
  (a2', a1', g') <- articulate g a'
  (h, f1) <- instantiateL g' a1' a1
  (d, f2) <- instantiateR h (substCtx h a2) a2'
  pure (d, funCo (a1, a2) (TyEVar a1', TyEVar a2') f1 f2)
instantiateR g a a' = case isMonoType a of
  Just t -> do
    wfMono g t
    g' <- maybe (throwError "solve failed") pure (solve a' t g)
    pure (g', ReflCo (fromMono t))
  Nothing -> error "unreachable: non-monotypes and monotypes both covered"


-- Thoughts regarding elaboration:
-- * TmTApp' is probably introduce in the 'app' judgement, when eliminating a
-- forall type.
-- * TmTLam' is probably introduced when an EntryUVar goes out of scope.

check :: Context -> Term -> Type -> M (Term', Context)
check g e (TyForall aa a) = do
  (e', dh) <- check (g :>: EntryUVar aa) e a
  let d = discardUVar dh aa
  pure (TmTLam' aa e', d)
check g TmUnit TyUnit = pure (TmUnit', g)
check g (TmLam x e) (TyArr a b) = do
  (e', dh) <- check (g :>: EntryVar x a) e b
  let d = discardVar dh x
  pure (TmLam' x a e', d)
check g e b = do
  (e', a, h) <- infer g e
  (d, f) <- subtype h (substCtx h a) (substCtx h b)
  pure (appCo f e', d)

infer :: Context -> Term -> M (Term', Type, Context)
infer g (TmVar x) = do
  a <- lookupVar g x
  pure (TmVar' x, a, g)
infer g (TmAnn e a) = do
  (e', d) <- check g e a
  pure (e', a, d) -- Elaborated IR does not need type annotations
infer g TmUnit = pure (TmUnit', TyUnit, g)
infer g (TmApp e1 e2) = do
  (e1', a, h) <- infer g e1
  (tys, e2', c, d) <- app h (substCtx h a) e2
  -- Hmm. This sort of works, but the tyvar in the type argument goes out of
  -- scope before it gets substituted.
  -- I think I need to generally have a "modify term when entries go out of
  -- scope" thing.
  -- EntryUVar dropped -> Intro tylam?
  -- EntryEVar dropped -> subst?
  pure (TmApp' (foldl TmTApp' e1' tys) e2', c, d)
infer g (TmLam x e) = do
  a' <- newEVar
  b' <- newEVar
  (e', dh) <- check (g :>: EntryEVar a' :>: EntryEVar b' :>: EntryVar x (TyEVar a')) e (TyEVar b')
  let d = discardVar dh x
  pure (TmLam' x (TyEVar a') e', TyArr (TyEVar a') (TyEVar b'), d)

-- Hmm. Return list of type arguments applied? Yep. Need it to elaborate
-- function application in 'infer'.
--
-- Inputs: initial context, subject type, argument term
-- Outputs: list of type arguments, argument term, result type, final context
app :: Context -> Type -> Term -> M ([Type], Term', Type, Context)
app g (TyForall aa a) e = do
  a' <- newEVar
  (tys, e', c, d) <- app (g :>: EntryEVar a') (open a aa a') e
  -- apply type argument (TyEVar a') here? (but e' is elaboration of the
  -- argument, not the function. Hmm.
  pure (TyEVar a' : tys, e', c, d)
app g (TyArr a c) e = do
  (e', d) <- check g e a
  pure ([], e', c, d)
app g (TyEVar a') e = do
  (a2', a1', g') <- articulate g a'
  (e', d) <- check g' e (TyEVar a1')
  pure ([], e', TyEVar a2', d)
app _ TyUnit _ = throwError "'unit' cannot have argument applied to it"
app _ (TyUVar _) _ = throwError "rigid type variable cannot have argument applied to it"


-- | Assert that a monotype is well-formed w.r.t. a context.
wfMono :: Context -> Mono -> M ()
wfMono _g _t = pure () -- fill this in.


-- Random idea: algorithmic inference as an arrow. I'm not really sure what
-- that would look like, though.
--
-- type Arr a b = (Context, a) -> E (Context, b) ? (thread context through)
-- type Arr a b = a -> E b ? (Just kliesli)


inferProgram :: Term -> Either String (Term', Type, Context)
inferProgram e = runExcept $ flip evalStateT 0 $ runM $ infer Empty e

-- ((\f -> f ()) : (forall x. x -> x) -> ()) (\a -> a)
-- Should elaborate to
-- (λ (f : forall x. x -> x) → f @unit ()) (Λ @(z : *) → λ (a : z) → a)
-- (Currently does not, as it does not insert type applications or
-- abstractions.)
demo :: Term
demo = TmApp (TmAnn e1 t2) e2
  where
    e1 :: Term
    e1 = TmLam f (TmApp (TmVar f) TmUnit)
    t1 :: Type
    t1 = TyForall x (TyArr (TyUVar x) (TyUVar x))
    t2 :: Type
    t2 = TyArr t1 TyUnit
    e2 :: Term
    e2 = TmLam a (TmVar a)
    f = Var "f"; x = UVar "x"; a = Var "a"

-- Debug purposes, mostly.
main :: IO ()
main = do
  -- \x -> \f -> f x
  -- - : forall a. forall b. a -> (a -> b) -> b
  -- (No generalization done, though)
  let e :: Term; e = (TmLam (Var "x") (TmLam (Var "f") (TmApp (TmVar (Var "f")) (TmVar (Var "x")))))
  case inferProgram demo of
    Left err -> do
      putStrLn "error:"
      print err
    Right (e', t, d) -> do
      putStrLn "ok:"
      putStrLn $ pprintContext d ++ " |- " ++ pprintType 0 t
      putStrLn $ pprintType 0 (substCtx d t)
      putStrLn $ pprintTerm' 0 e'

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
pprintType _ TyUnit = "unit"
pprintType p (TyArr a b) = parensIf (p > 5) $ pprintType 6 a ++ " -> " ++ pprintType 5 b
pprintType p (TyForall aa a) = parensIf (p > 0) $ "forall " ++ show aa ++ ". " ++ pprintType 0 a
pprintType _ (TyUVar aa) = show aa
pprintType _ (TyEVar a') = show a'

pprintMono :: Int -> Mono -> String
pprintMono _ MonoUnit = "unit"
pprintMono p (MonoArr a b) = parensIf (p > 5) $ pprintMono 6 a ++ " -> " ++ pprintMono 5 b
pprintMono _ (MonoUVar aa) = show aa
pprintMono _ (MonoEVar a') = show a'

instance Show Var where
  show (Var x) = x

instance Show UVar where
  show (UVar aa) = aa

instance Show EVar where
  show (EVar i) = "#" ++ show i

parensIf :: Bool -> String -> String
parensIf False s = s
parensIf True s = "(" ++ s ++ ")"


pprintTerm' :: Int -> Term' -> String
pprintTerm' _ TmUnit' = "()"
pprintTerm' _ (TmVar' x) = show x
pprintTerm' p (TmApp' e1 e2) = parensIf (p > 9) $ pprintTerm' 9 e1 ++ " " ++ pprintTerm' 10 e2
pprintTerm' p (TmLam' x t e) =
  parensIf (p > 0) $ "λ (" ++ show x ++ " : " ++ pprintType 0 t ++ ") → " ++ pprintTerm' 0 e
pprintTerm' p (TmTApp' e t) = parensIf (p > 9) $ pprintTerm' 9 e ++ " @" ++ pprintType 10 t
pprintTerm' p (TmTLam' aa e) =
  parensIf (p > 0) $ "Λ (" ++ show aa ++ " : *) → " ++ pprintTerm' 0 e
