
module CPS.Simpl (simpl) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import CPS.IR


simpl :: TermK a -> TermK a
simpl t = fst $ simplify emptyEnv t
  where emptyEnv = SimplEnv Map.empty Map.empty


data SimplEnv
  = SimplEnv {
    -- The definitions map contains every variable in scope.
    -- If the variable is bound to a value (as in 'let x = v in e') the RHS is 'Just v'
    -- Otherwise, (as in 'let cont k x = e in e''), the RHS is 'Nothing'
    simplDefs :: Map TmVar (Maybe ValueK)
  , simplSubst :: Map TmVar TmVar
  }

lookupValue :: TmVar -> SimplEnv -> (TmVar, Maybe ValueK)
lookupValue x env@(SimplEnv def sub) = let x' = rename env x in case Map.lookup x' def of
  Nothing -> error "lookupValue: variable not in environment"
  Just v -> (x', v)

rename :: SimplEnv -> TmVar -> TmVar
rename (SimplEnv _ sub) x = case Map.lookup x sub of
  Nothing -> x
  Just x' -> x'

substVar :: Map TmVar TmVar -> TmVar -> TmVar
substVar sub x = maybe x id (Map.lookup x sub)

substValue :: Map TmVar TmVar -> ValueK -> ValueK
substValue _ NilK = NilK
substValue sub (PairK x y) = PairK (substVar sub x) (substVar sub y)

-- Pass the environment under a binder.
-- May rename things???
-- (If so, maintain in-scope set.)
-- TODO: Fix scoping in Simpl.
under :: TmVar -> SimplEnv -> SimplEnv
under x env = env

defineValue :: TmVar -> ValueK -> SimplEnv -> SimplEnv
defineValue x v (SimplEnv def sub) =
  let v' = substValue sub v in
  SimplEnv (Map.insert x (Just v') def) sub

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
-- (I think I might actually need ProductUsage SimplUsage [SimplUsage]: a usage
-- for the entire term, plus sub-usages for each subterm)
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

recordOne :: TmVar -> Census
recordOne x = Census (Set.singleton x)

recordList :: [TmVar] -> Census
recordList xs = Census (Set.fromList xs)

bind :: TmVar -> Census -> Census
bind x (Census xs) = Census (Set.delete x xs)

query :: TmVar -> Census -> SimplUsage
query x (Census xs) = if Set.member x xs then SomeUses else NoUses

ifLive :: TmVar -> (TermK a -> TermK a) -> (Census -> Census) -> (TermK a, Census) -> (TermK a, Census)
ifLive x rebuildTm rebuildCensus (e, census) = case query x census of
  NoUses -> (e, census)
  SomeUses -> (rebuildTm e, rebuildCensus census)

-- | Perform obvious beta-reductions, and then discard unused local bindings
-- afterward.
--
-- TODO: Annotate fun/cont definition with OneShot/MultiShot (for inlining)
simplify :: SimplEnv -> TermK a -> (TermK a, Census)
simplify env (HaltK x) =
  let x' = rename env x in
  (HaltK x', recordOne x')
simplify env (JumpK k xs) =
  -- Note: This assumes that a jump uses all its arguments.
  -- A more sophisticated analysis would require iterating to a fixpoint.
  let xs' = map (rename env) xs in
  (JumpK k xs', recordList xs')
simplify env (CallK f xs ks) =
  -- Note: This assumes that a function call uses all its arguments.
  -- A more sophisticated analysis would require iterating to a fixpoint.
  let xs' = map (rename env) xs in
  (CallK f xs' ks, recordList xs')
simplify env (CaseK x t ks) = simplifyCase env x t ks
-- If there is a binding y := (z, w), substitute x := z in e
simplify env (LetFstK x t y e) = 
  -- Check for redex
  case lookupValue y env of
    -- There is a redex: let x = fst (z1, z2) in e ~> e[x := z1]
    (y', Just (PairK z1 z2)) ->
      -- TODO: We are passing under the binder for 'x'. Wat do.
      -- I don't think *both* defineSubst and under should be used here.
      -- 'under' would be for passing under a variable that should not be touched;
      -- 'defineSubst' is used to eliminate occurrences of 'x'
      let env' = defineSubst x z1 (under x env) in
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
    (_, Just _) -> error "simplify: env contained invalid value for fst"
    -- No redex
    (y', Nothing) ->
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
simplify env (LetContK ks e) =
  let f (kont, cen) (ks', census) = (kont : ks', cen <> census) in
  let (ks', census) = foldr f ([], mempty) (map (simplifyContDef env) ks) in
  -- Shouldn't I be bringing the 'ks' into scope here?
  -- I guess not, the SimplEnv doesn't have any fields for cont-stuff.
  let (e', census') = simplify env e in
  (LetContK ks' e', census <> census')

simplifyVal :: SimplEnv -> ValueK -> (ValueK, Census)
simplifyVal env (PairK y z) =
  let y' = rename env y; z' = rename env z in (PairK y' z', recordList [y', z'])
simplifyVal env (InlK y) = let y' = rename env y in (InlK y', recordOne y')
simplifyVal env (InrK z) = let z' = rename env z in (InrK z', recordOne z')
simplifyVal _ NilK = (NilK, mempty)
simplifyVal _ (IntValK i) = (IntValK i, mempty)
simplifyVal _ (BoolValK b) = (BoolValK b, mempty)

simplifyArith :: SimplEnv -> ArithK -> Either (ArithK, Census) Int
simplifyArith env op = arith (renameOp op)
  where
    renameOp (AddK x y) = (AddK, (+), x, y)
    renameOp (SubK x y) = (SubK, (-), x, y)
    renameOp (MulK x y) = (MulK, (*), x, y)
    -- renameOp (NegK x) = (NegK

    arith (g, f, x, y) = case (lookupValue x env, lookupValue y env) of
      ((_, Just (IntValK i)), (_, Just (IntValK j))) -> Right (f i j)
      ((x', _), (y', _)) -> Left (g x' y', recordList [x', y'])

simplifyContDef :: SimplEnv -> ContDef a -> (ContDef a, Census)
simplifyContDef env (ContDef ann k xs e) =
  -- Pass under xs binders
  let env' = foldr (under . fst) env xs in
  let (e', census) = simplify env' e in
  let census' = foldr (bind . fst) census xs in
  (ContDef ann k xs e', census')

-- | Perform beta-reduction for a case expression
simplifyCase :: SimplEnv -> TmVar -> TyConApp -> [(Ctor, CoVar)] -> (TermK a, Census)
simplifyCase env x (CaseSum ta tb) [k1, k2] =
  case lookupValue x env of
    (_, Just (InlK y)) -> (JumpK (snd k1) [y], recordOne y)
    (_, Just (InrK z)) -> (JumpK (snd k2) [z], recordOne z)
    (_, Just _) -> error "simplifyCase: env contained invalid value for sum type"
    (x', Nothing) -> (CaseK x' (CaseSum ta tb) [k1, k2], recordOne x')
simplifyCase _ _ (CaseSum _ _) _ = error "simplifyCase: incorrect number of branches for sum type"
simplifyCase env x CaseBool [k1, k2] =
  case lookupValue x env of
    (_, Just (BoolValK True)) -> (JumpK (snd k1) [], mempty)
    (_, Just (BoolValK False)) -> (JumpK (snd k2) [], mempty)
    (_, Just _) -> error "simplifyCase: env contained invalid value for bool type"
    (x', Nothing) -> (CaseK x' CaseBool [k1, k2], recordOne x')
simplifyCase _ _ CaseBool _ = error "simplifyCase: incorrect number of branches for bool type"
simplifyCase _ _ _ _ = error "simplifyCase: cannot perform case analysis on this type"

-- data Usage = MustKeep | ProductUsage Usage Usage | CanDiscard
-- data ParamUsage = ParamUsage { tmParamUsage :: Map TmVar Usage, coParamUsage :: Map CoVar Usage }
-- -- Annotate each function/continuation parameter with how it is used in the
-- -- body, to identify parameters that can be discarded.
-- -- Must iterate to fixpoint
-- markParamUsage :: TermK a -> TermK ParamUsage
-- -- Use the parameter info to remove unused parameters, and rewrite the call sites.
-- removeUnusedParams :: TermK ParamUsage -> TermK ()

