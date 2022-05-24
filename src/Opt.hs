{-# LANGUAGE StandaloneDeriving, DerivingVia, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Opt where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Int
import Data.Traversable (for)

import Control.Monad.Reader
import Control.Monad.Writer

import CPS (TermK(..), TmVar(..), CoVar(..), FunDef(..), ContDef(..), ValueK(..), TypeK(..), ArithK(..))

-- [Compiling with Continuations, Continued] mostly.
-- CPS transformation, Closure Conversion, hopefully C code generation.

-- TODO: Annotate function and continuation definitions with useful information.
-- * Number of occurrences
-- * Availability for inlining
-- * Call patterns
-- * Usage/abscence/forcing of each argument


-- TODO: Figure out call-pattern specialization
-- contify is basically call-pattern specialization for continuation arguments?
-- TODO: Implement Call Arity to be smarter about passing multiple arguments
-- together.
-- TODO: Break Opt.hs into Opt/*.hs: split out specific optimizations
-- (Or, if I have optimizations for other phases (e.g., source, CC, etc.),
-- Phase/Opt.hs and Phase/Opt/*.hs)

newtype InlineM a = InlineM { runInlineM :: Reader InlineEnv a }

deriving newtype instance Functor InlineM
deriving newtype instance Applicative InlineM
deriving newtype instance Monad InlineM
deriving newtype instance MonadReader InlineEnv InlineM

data InlineEnv
  = InlineEnv {
  -- | Functions and continuations larger than the threshold will not be
  -- inlined.
  -- TODO: different threshold for fun/cont?
    inlineSizeThreshold :: Int

  -- | If a continuation variable has an unfolding, it is stored here.
  , inlineCoDefs :: Map CoVar (ContDef ())
  -- | If a function has an unfolding, it is stored here.
  , inlineFnDefs :: Map TmVar (FunDef ())

  -- | Values are bound here, so that beta-redexes can reduce.
  , inlineValDefs :: Map TmVar ValueK

  -- | A substitution on term variables, used when beta-reducing and unfolding.
  , inlineTmSub :: Map TmVar TmVar
  -- | A substitution on term variables, used when beta-reducing and unfolding.
  , inlineCoSub :: Map CoVar CoVar
  }

withTmSub :: (TmVar, TmVar) -> InlineM a -> InlineM a
withTmSub (x, y) m = local f m
  where
    f env = env { inlineTmSub = Map.insert x y (inlineTmSub env) }

withCoSub :: (CoVar, CoVar) -> InlineM a -> InlineM a
withCoSub (x, y) m = local f m
  where
    f env = env { inlineCoSub = Map.insert x y (inlineCoSub env) }

withVal :: TmVar -> ValueK -> InlineM a -> InlineM a
withVal x v m = local f m
  where
    f env = env { inlineValDefs = Map.insert x v (inlineValDefs env) }

withFn :: FunDef () -> InlineM a -> InlineM a
withFn fn@(FunDef () f _ _ _) m = local g m
  where
    g env = env { inlineFnDefs = Map.insert f fn (inlineFnDefs env) }

withCont :: ContDef () -> InlineM a -> InlineM a
withCont kont@(ContDef () k _ _) m = local g m
  where
    g env = env { inlineCoDefs = Map.insert k kont (inlineCoDefs env) }

appTmSub :: TmVar -> InlineM TmVar
appTmSub x = do
  env <- ask
  case Map.lookup x (inlineTmSub env) of
    Nothing -> pure x
    Just y -> pure y

appCoSub :: CoVar -> InlineM CoVar
appCoSub k = do
  env <- ask
  case Map.lookup k (inlineCoSub env) of
    Nothing -> pure k
    Just k' -> pure k'

-- | Inline definitions and simplify redexes.
inlineK :: TermK () -> InlineM (TermK ())
-- Occurrences get inlined if their definition is in the environment.
-- (TODO: Inline decision based on context of occurrence, not just context of
-- definition?)
inlineK (JumpK k xs) = do
  env <- ask
  case Map.lookup k (inlineCoDefs env) of
    Nothing -> pure (JumpK k xs)
    Just (ContDef () _ [(y, _)] e) -> withTmSub (y, xs !! 0) $ inlineK e
inlineK (CallK f [x] [k]) = do
  env <- ask
  case Map.lookup f (inlineFnDefs env) of
    Nothing -> pure (CallK f [x] [k])
    Just (FunDef () _ [(y, _)] [(k', _)] e) -> withCoSub (k', k) $ withTmSub (y, x) $ inlineK e
-- Eliminators use 'inlineValDefs' to beta-reduce, if possible.
-- (A function parameter will not reduce, e.g.)
-- Actually, isn't reducing @case inl x of ...@ and @fst (x, y)@ the
-- responsibility of 'simplify', not 'inlineK'?
inlineK (CaseK x [(k1, s1), (k2, s2)]) = do
  x' <- appTmSub x
  env <- ask
  case Map.lookup x' (inlineValDefs env) of
    Just (InlK y) -> inlineK (JumpK k1 [y])
    Just (InrK y) -> inlineK (JumpK k2 [y])
    Just _ -> error "case on non-inj value"
    Nothing -> pure (CaseK x' [(k1, s1), (k2, s2)])
inlineK (LetFstK x t y e) = do
  y' <- appTmSub y
  env <- ask
  -- We need to rebuild the LetFstK here because there still might be some
  -- variable that refers to it.
  -- TODO: Use usage information to discard dead bindings.
  case Map.lookup y' (inlineValDefs env) of
    Just (PairK p _) -> LetFstK x t y' <$> withTmSub (x, p) (inlineK e)
    Just _ -> error "fst on non-pair value"
    Nothing -> LetFstK x t y' <$> inlineK e
inlineK (LetSndK x t y e) = do
  y' <- appTmSub y
  env <- ask
  -- We need to rebuild the LetFstK here because there still might be some
  -- variable that refers to it.
  -- A DCE pass can remove it later.
  case Map.lookup y' (inlineValDefs env) of
    Just (PairK _ q) -> LetSndK x t y' <$> withTmSub (x, q) (inlineK e)
    Just _ -> error "snd on non-pair value"
    Nothing -> LetFstK x t y' <$> inlineK e
-- Functions and continuations are the things that need to be inlined.
-- These two cases decide whether or not a binding should be added to the environment.
-- When extending the environment:
-- * take a census (count how many occurrences of the bound variable, while
--   also reducing beta-redexes on the way)
-- * If 0 occurrences (after reduction), discard.
-- * If 1 occurrence, always inline
-- * If >1 occurrence, inline if small
--   (Or if would reduce? Maybe census collects argument patterns instead)
-- TODO: This is still incorrect if the binding is self-recursive.
-- TODO: Use loop-breakers to inline recursive bind groups.
inlineK (LetContK ks e) = case ks of
  [] -> inlineK e
  [k] -> LetContK ks <$> withCont k (inlineK e)
  _ -> LetContK ks <$> inlineK e
inlineK (LetFunK fs e) = case fs of
  [] -> inlineK e
  [f] -> LetFunK fs <$> withFn f (inlineK e)
  _ -> LetFunK fs <$> inlineK e
-- Value bindings are added to 'inlineValDefs', so they can be reduced.
inlineK (LetValK x t v e) = LetValK x t v <$> withVal x v (inlineK e)

-- Secrets of GHC Inliner:
-- data Usage = LoopBreaker | Dead | OnceSafe | MultiSafe | OnceUnsafe | MultiUnsafe
data Usage
  -- variable occurs zero times in body
  = Unused
  -- variable occurs up to once in all paths. (e.g., once on one path, never on the other)
  -- (Actually, does this make sense when considering case-continuations?)
  | AffineUsage
  -- variable occurs more than once
  | ManyUsage

-- -- | Count occurrences and pick loop breakers, annotating binders with usage
-- -- information.
-- countOccurrences :: TermK a -> (TermK Usage, Map TmVar Usage, Map CoVar Usage)
-- -- TODO: We're mostly trying to count continuation/function occurrences, right?
-- -- Do we really need to count the arguments?
-- -- Hmm. Probably. Consider `let fun f = ...; in k f` That's a use of `k` and a
-- -- use of `f`.
-- countOccurrences (JumpK k xs) = (JumpK k xs, Map.singleton k _, Map.singleton x _)
-- countOccurrences (CallK f xs ks) = (CallK f xs ks, _, _)
-- -- Somehow merge the occurrences from each branch.
-- -- Also, I think that the case branch continuations are particularly
-- -- second-class, so it may be possible to treat them specially.
-- countOccurrences (CaseK x k1 k2) = (CaseK x k1 k2, Map.singleton x _, Map.fromList [(k1, _), (k2, _)])
-- countOccurrences (LetFstK x t y e) =
--   let (e', tms, cos) = countOccurrences e in
--   (LetFstK x t y e', Map.insert y _ (Map.delete x tms), cos)
-- countOccurrences (LetContK ks e) = _

-- TODO: Count occurrences of covariables as well.
-- countOccurrences :: Map TmVar ValueK -> Set TmVar -> TermK -> (TermK, Map TmVar Int)
-- If y in vs, that's an occurrence.
-- If y := (p, q) in env, substitute x := p, discard let x = fst y.
-- countOccurrences vs (LetFstK x y e) = _

-- Count number of 'let' bindings, recursively.
sizeK :: TermK () -> Int
sizeK (LetFunK fs e) = sum (map (\ (FunDef () f _ _ e') -> sizeK e') fs) + sizeK e
sizeK (LetValK x _ v e) = 1 + sizeK e


-- Higher-order functions can be eliminated using monomorphization
-- (I don't think I need this, because I can do closures+function pointers)


data SimplEnv = SimplEnv { simplValues :: Map TmVar ValueK, simplSubst :: Map TmVar TmVar }

rename :: SimplEnv -> TmVar -> TmVar
rename (SimplEnv _ sub) x = case Map.lookup x sub of
  Nothing -> x
  Just x' -> x'

-- Pass the environment under a binder.
-- May rename things???
-- (If so, maintain in-scope set.)
-- TODO: Fix scoping in Simpl.
under :: TmVar -> SimplEnv -> SimplEnv
under x env = env

defineValue :: TmVar -> ValueK -> SimplEnv -> SimplEnv
defineValue x v (SimplEnv def sub) = SimplEnv (Map.insert x v def) sub

defineSubst :: TmVar -> TmVar -> SimplEnv -> SimplEnv
defineSubst x y (SimplEnv def sub) = SimplEnv def (Map.insert x y sub)

-- For DCE of assignment statements, we only really care about "some uses"
-- (can't DCE) or "no uses" (can DCE). "One use" isn't important because we
-- already reduced beta-redexes, so we can't inline variables further (only
-- functions, etc.)
--
-- (On the other hand, it probably would be useful to give more refined usage
-- information to the function parameters? for worker-wrapper and stuff,
-- maybe?)
-- (e.g., ProductUsage SimplUsage SimplUsage. let z = fst p + snd p would give
-- (ProductUsage SomeUses SomeUses), but let z = snd p + 3 would give
-- (ProductUsage NoUses SomeUses)) (I think I would need to refine the lattice)
data SimplUsage
  = NoUses
  | SomeUses

-- | A 'Census' counts what variables are used in a term (and sort of how many
-- times they are used). This is important for DCE, WW, and probably inlining.
newtype Census = Census (Set TmVar)

deriving newtype instance Semigroup Census
deriving newtype instance Monoid Census

-- TODO: Probably need covariable occurrences? Not for beta-reduction, at least.
-- Covariable occurrences are necessary for inlining, though.
record :: TmVar -> Census -> Census
record x (Census xs) = Census (Set.insert x xs)

bind :: TmVar -> Census -> Census
bind x (Census xs) = Census (Set.delete x xs)

query :: TmVar -> Census -> SimplUsage
query x (Census xs) = if Set.member x xs then SomeUses else NoUses

-- | Perform obvious beta-reductions, and then discard unused local bindings
-- afterward.
--
-- TODO: Annotate fun/cont definition with OneShot/MultiShot (for inlining)
simplify :: SimplEnv -> TermK a -> (TermK a, Census)
simplify env (HaltK x) =
  let x' = rename env x in
  (HaltK x', record x' mempty)
simplify env (JumpK k xs) =
  -- Note: This assumes that a jump uses all its arguments.
  -- A more sophisticated analysis would require iterating to a fixpoint.
  let xs' = map (rename env) xs in
  (JumpK k xs', foldr record mempty xs')
simplify env (CallK f xs ks) =
  -- Note: This assumes that a function call uses all its arguments.
  -- A more sophisticated analysis would require iterating to a fixpoint.
  let xs' = map (rename env) xs in
  (CallK f xs' ks, foldr record mempty xs')
simplify env (CaseK x [(k1, s1), (k2, s2)]) =
  let x' = rename env x in
  case Map.lookup x' (simplValues env) of
    Just (InlK y) -> (JumpK k1 [y], record y mempty)
    Just (InrK z) -> (JumpK k2 [z], record z mempty)
    Just (BoolValK b) -> (JumpK (if b then k1 else k2) [], mempty)
    _ ->
      (CaseK x' [(k1, s1), (k2, s2)], record x' mempty)
-- If there is a binding y := (z, w), substitute x := z in e
simplify env (LetFstK x t y e) = 
  -- Apply substitution
  let y' = rename env y in
  -- Check for redex
  case Map.lookup y' (simplValues env) of
    -- There is a redex: let x = fst (z1, z2) in e ~> e[x := z1]
    Just (PairK z1 z2) ->
      -- TODO: We are passing under the binder for 'x'. Wat do.
      let env' = defineSubst x z1 (under x env) in
      -- let env' = env { simplSubst = Map.insert x z1 (simplSubst env) } in
      let (e', census) = simplify env' e in
      case query x census of
        -- No uses of this variable. Discard it.
        -- The census of variable occurrences is unchanged.
        NoUses -> (e', census)
        -- cannot discard x.
        SomeUses ->
          -- Free occurrences of x in e' now refer to this binding.
          -- there is an occurrence of y'.
          let census' = record y' (bind x census) in
          (LetFstK x t y' e', census')
    -- No redex
    _ ->
      let env' = under x env in
      let (e', census) = simplify env' e in
      let census' = record y' (bind x census) in
      (LetFstK x t y' e', census')
simplify env (LetValK x t v e) =
  let (v', census) = simplifyVal env v in
  let env' = defineValue x v (under x env) in
  let (e', census') = simplify env' e in
  case query x census' of
    NoUses -> (e', census')
    SomeUses -> (LetValK x t v' e', census <> bind x census')
-- if y := int, z := int, rewrite to let x = int(y op z) in ...
-- If only one is an integer, it is still possible to commute/assoc to simplify
-- arithmetic expressions. Maybe later.
simplify env (LetArithK x op e) =
  case simplifyArith env op of
    -- Could not simplify
    Left (op', census) ->
      let env' = under x env in -- pass under x
      let (e', census') = simplify env' e in
      case query x census' of
        NoUses -> (e', census')
        SomeUses -> (LetArithK x op' e', census <> bind x census')
    -- Simplified to an integer
    Right i ->
      let env' = defineValue x (IntValK i) (under x env) in
      let (e', census) = simplify env' e in
      case query x census of
        NoUses -> (e', census)
        SomeUses -> (LetValK x IntK (IntValK i) e', bind x census)
-- if y := int, rewrite 'let x = -y in e' into 'let x = -int in e'.
simplify env (LetNegateK x y e) =
  case Map.lookup (rename env x) (simplValues env) of
    Just (IntValK i) ->
      let i' = negate i in
      let env' = defineValue x (IntValK i') (under x env) in
      let (e', census) = simplify env' e in
      case query x census of
        NoUses -> (e', census)
        SomeUses -> (LetValK x IntK (IntValK i') e', bind x census)
    _ ->
      let env' = under x env in
      let (e', census) = simplify env' e in
      case query x census of
        NoUses -> (e', census)
        SomeUses -> (LetNegateK x (rename env y) e', bind x census)
simplify env (LetContK ks e) =
  let f (kont, cen) (ks', census) = (kont : ks', cen <> census) in
  let (ks', census) = foldr f ([], mempty) (map (simplifyContDef env) ks) in
  let (e', census') = simplify env e in
  (LetContK ks' e', census <> census')

simplifyVal :: SimplEnv -> ValueK -> (ValueK, Census)
simplifyVal env (PairK y z) =
  let (y', z') = (rename env y, rename env z) in (PairK y' z', record y' (record z' mempty))
simplifyVal env (InlK y) = let y' = rename env y in (InlK y', record y' mempty)
simplifyVal env (InrK z) = let z' = rename env z in (InrK z', record z' mempty)
simplifyVal _ NilK = (NilK, mempty)
simplifyVal _ (IntValK i) = (IntValK i, mempty)
simplifyVal _ (BoolValK b) = (BoolValK b, mempty)

simplifyArith :: SimplEnv -> ArithK -> Either (ArithK, Census) Int
simplifyArith env op = simpl (renameOp op)
  where
    renameOp (AddK x y) = (AddK, (+), rename env x, rename env y)
    renameOp (SubK x y) = (SubK, (-), rename env x, rename env y)
    renameOp (MulK x y) = (MulK, (*), rename env x, rename env y)

    simpl (g, f, x', y') = case (Map.lookup x' (simplValues env), Map.lookup y' (simplValues env)) of
      (Just (IntValK i), Just (IntValK j)) -> Right (f i j)
      (_, _) -> Left (g x' y', record x' (record y' mempty))

simplifyContDef :: SimplEnv -> ContDef a -> (ContDef a, Census)
simplifyContDef env (ContDef ann k xs e) =
  -- Pass under xs binders
  let env' = foldr (under . fst) env xs in
  let (e', census) = simplify env' e in
  let census' = foldr (bind . fst) census xs in
  (ContDef ann k xs e', census')

-- data Usage = MustKeep | ProductUsage Usage Usage | CanDiscard
-- data ParamUsage = ParamUsage { tmParamUsage :: Map TmVar Usage, coParamUsage :: Map CoVar Usage }
-- -- Annotate each function/continuation parameter with how it is used in the
-- -- body, to identify parameters that can be discarded.
-- -- Must iterate to fixpoint
-- markParamUsage :: TermK a -> TermK ParamUsage
-- -- Use the parameter info to remove unused parameters, and rewrite the call sites.
-- removeUnusedParams :: TermK ParamUsage -> TermK ()


-- * Flatten product arguments into multiple parameters.
--
-- Could be smarter, by using usage/absence information (special case of
-- worker-wrapper)
-- (Furthermore, there should be heuristics for when to apply this)
-- (e.g., flatten if the original variable is only projected from, not used
-- directly)
--
-- Rewrite
--   fun f (p : int * (bool * unit)) : int = e
-- into
--   fun f (x : int, y : bool, z : unit) : int =
--     let t0 = (y, z) in
--     let p = (x, t0) in
--     e
-- 
-- And the call site 'f q' into
--   let x0 = fst q in
--   let x1 = snd q in
--   let x2 = fst x1 in
--   let x3 = snd x1 in
--   f x0 x2 x3
--
-- (The simplified should run afterwards, to clean up)
--
-- This optimization should probably also run on continuation definitions.

-- | Decompose a product type by labelling all its subterms.
-- Invariant: the 'TypeK' in 'NotProduct' is not constructed using 'ProdK'.
-- (Actually, nothing bad happens. It may even be beneficially, for partial
-- flattening)
data LabelledProduct
  = NotProduct TypeK
  | IsProduct TmVar LabelledProduct TmVar LabelledProduct

unlabel :: LabelledProduct -> TypeK
unlabel (NotProduct t) = t
unlabel (IsProduct _ t1 _ t2) = ProdK (unlabel t1) (unlabel t2) 

-- TODO: I need a supply of locally?-fresh names here.
-- labelProduct :: Monad m => TypeK -> m LabelledProduct
-- labelProduct (ProdK t1 t2) = _
-- labelProduct t = pure (NotProduct t)

-- | Label a function definition with its flattened arguments
-- Other functions can use this annotation to transform the body and call sites.
-- labelDefinition :: SomeMonad m => FunDef a -> m (FunDef [(TmVar, LabelledProduct)])
-- labelDefinition fun = pure fun

-- | After flattening the argument list, we need to rebuild the original value,
-- because the body uses it.
-- (the simplifier will clean this up, usually. If it doesn't, the optimizer
-- should be less zealous)
rebuildDefinition :: (TmVar, LabelledProduct) -> Endo (TermK ())
-- Nothing to do: x : t is already in scope
rebuildDefinition (x, NotProduct t) = mempty
rebuildDefinition (x, IsProduct y1 t1 y2 t2) =
-- Need to reconstitute x : t1 * t2 from y1 : t1 and y2 : t2 with a pair constructor
  rebuildDefinition (y1, t1) <>
    rebuildDefinition (y2, t2) <>
      Endo (LetValK x (ProdK (unlabel t1) (unlabel t2)) (PairK y1 y2))

rebuildDefinitions :: [(TmVar, LabelledProduct)] -> Endo (TermK ())
rebuildDefinitions prods = foldMap rebuildDefinition prods

-- flattenFunDef :: FunDef a -> FunDef a
-- flattenFunDef (FunDef ann f xs ks e) = FunDef ann f xs' ks e'
--   where
--     prods = _
--     xs' = concatMap _ (productLeaves prods)
--     e' = _ -- rebuild parameter list, transform call sites

-- Turn 'bind (p : t1 * t2) in e' into 'bind (x : t1, y : t2) in let p = (x, y) in e'
-- flattenBinder :: [(TmVar, TypeK)] -> TermK () -> TermK ()
-- flattenBinder xs e = _


-- | Given an argument descibed by a product type, flatten it into components.
-- This produces an endomorphism (to add the required projection statements),
-- and a list of parameters.
flattenArgument :: (TmVar, LabelledProduct) -> (Endo (TermK ()), [TmVar])
flattenArgument (x, NotProduct t) = (mempty, [x])
flattenArgument (p, IsProduct y1 t1 y2 t2) = mconcat [
    -- Hmm. This only ever generates arguments for each leaf.
    -- Are there situations where intermediate values are still useful?
    -- Can this be adjusted to produce those?
    (Endo (LetFstK y1 (unlabel t1) p), mempty)
  , flattenArgument (y1, t1)
  , (Endo (LetSndK y2 (unlabel t2) p), mempty)
  , flattenArgument (y2, t2)
  ]

flattenCallSite :: TmVar -> [(TmVar, LabelledProduct)] -> [CoVar] -> TermK ()
flattenCallSite fn prods ks =
  let (Endo build, xs') = foldMap flattenArgument prods in
  build (CallK fn xs' ks)

flattenJumpSite :: CoVar -> [(TmVar, LabelledProduct)] -> TermK ()
flattenJumpSite co prods =
  let (Endo build, xs') = foldMap flattenArgument prods in
  build (JumpK co xs')
