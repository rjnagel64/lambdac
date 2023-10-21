
module CPS.OneShot (inlineOneShot) where

import CPS.IR hiding (Subst)

import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe (catMaybes)
import Data.Traversable (for, mapAccumL)
import Data.Bifunctor
import Prelude hiding (cos)

-- a cps optimization pass that inlines (well-known?) one-shot continuations
-- this should eliminate *most* of the nesting from long let-chains.

-- NeverUsed <= UsedOnce <= ManyUses
-- discard if NeverUsed, inline if UsedOnce, leave alone if ManyUses


inlineOneShot :: Program -> Program
inlineOneShot (Program ds e) = runM $ do
  e' <- inlineTerm e
  pure (Program ds e')

inlineTerm :: TermK -> M TermK
inlineTerm (HaltK x) = pure (HaltK x)
inlineTerm (JumpK (CoVarK k) xs) = do
  env <- asks envConts
  case Map.lookup k env of
    Just cont -> pure (applyContDef cont xs)
    Nothing -> pure (JumpK (CoVarK k) xs)
-- TODO(later): Inline one-shot functions as well
inlineTerm (CallK f xs ks) = do
  ks' <- for ks $ \case
    CoVarK k -> do
      env <- asks envConts
      case Map.lookup k env of
        Just cont -> pure (ContValK cont)
        Nothing -> pure (CoVarK k)
    ContValK cont -> do
      cont' <- inlineCont cont
      pure (ContValK cont')
  pure (CallK f xs ks')
inlineTerm (IfK x k1 k2) = do
  k1' <- inlineCont k1
  k2' <- inlineCont k2
  pure (IfK x k1' k2')
inlineTerm (CaseK x tcapp alts) = do
  alts' <- for alts $ \ (c, coval) -> do
    coval' <- inlineCoValue coval
    pure (c, coval')
  pure (CaseK x tcapp alts')
inlineTerm (LetContK ks e) = do
  let usage = countUses e
  (ks', defs) <- fmap unzip $ for ks $ \ (k, cont) -> do
    case lookupCoUsage k usage of
      NeverUsed ->
        -- discard cont binding, nothing to inline
        pure (Nothing, Nothing)
      UsedOnce -> do
        -- discard cont binding, inline it at its singular use site
        cont' <- inlineCont cont
        pure (Nothing, Just (k, cont'))
      ManyUses -> do
        -- maintain cont binding, do not inline
        cont' <- inlineCont cont
        pure (Just (k, cont'), Nothing)
  e' <- withContDefs (catMaybes defs) $ inlineTerm e
  let ks'' = catMaybes ks'
  if null ks'' then
    pure e'
  else
    pure (LetContK ks'' e')
inlineTerm (LetFunK fs e) = do
  fs' <- for fs $ \f -> inlineFunDef f
  -- Not going to bother with one-shot funcs (but I could)
  e' <- inlineTerm e
  pure (LetFunK fs' e')
inlineTerm (LetValK x t v e) = do
  e' <- inlineTerm e
  pure (LetValK x t v e')
inlineTerm (LetFstK x t y e) = do
  e' <- inlineTerm e
  pure (LetFstK x t y e')
inlineTerm (LetSndK x t y e) = do
  e' <- inlineTerm e
  pure (LetSndK x t y e')
inlineTerm (LetFieldK x t y f e) = do
  e' <- inlineTerm e
  pure (LetFieldK x t y f e')
inlineTerm (LetArithK x op e) = do
  e' <- inlineTerm e
  pure (LetArithK x op e')
inlineTerm (LetCompareK x op e) = do
  e' <- inlineTerm e
  pure (LetCompareK x op e')
inlineTerm (LetStringOpK x t op e) = do
  e' <- inlineTerm e
  pure (LetStringOpK x t op e')
inlineTerm (LetBindK x y op e) = do
  e' <- inlineTerm e
  pure (LetBindK x y op e')

inlineCont :: ContDef -> M ContDef
inlineCont (ContDef xs e) = do
  -- Hmm. probably needs to introduce xs
  e' <- inlineTerm e
  pure (ContDef xs e')

inlineFunDef :: FunDef -> M FunDef
inlineFunDef (FunDef f xs ks e) = do
  e' <- inlineTerm e
  pure (FunDef f xs ks e')

inlineCoValue :: CoValueK -> M CoValueK
inlineCoValue (CoVarK k) = pure (CoVarK k)
inlineCoValue (ContValK cont) = ContValK <$> inlineCont cont


applyContDef :: ContDef -> [ValueK] -> TermK
applyContDef (ContDef xs e) as =
  let sub = makeJumpSubst xs as in
  subst sub e


newtype M a = M { getM :: Reader Env a }

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader Env M

data Env = Env { envConts :: Map CoVar ContDef }

emptyEnv :: Env
emptyEnv = Env { envConts = Map.empty }

runM :: M a -> a
runM m = flip runReader emptyEnv $ getM m

withContDefs :: [(CoVar, ContDef)] -> M a -> M a
withContDefs ks m = local extend m
  where extend env = env { envConts = insertMany ks (envConts env) }

insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs


data Use = NeverUsed | UsedOnce | ManyUses
  deriving (Eq, Ord) -- ord should be w.r.t. Monoid, but the derived version gives same answer

-- hmm. consider: semiring, instead/in addition to Monoid
-- ((*) for multiple uses together, (+) for alternate paths?)
instance Semigroup Use where
  NeverUsed <> x = x
  x <> NeverUsed = x
  UsedOnce <> UsedOnce = ManyUses
  UsedOnce <> ManyUses = ManyUses
  ManyUses <> UsedOnce = ManyUses
  ManyUses <> ManyUses = ManyUses

instance Monoid Use where
  mempty = NeverUsed

data Usage = Usage (Map TmVar Use) (Map CoVar Use)

instance Semigroup Usage where
  Usage tm1 co1 <> Usage tm2 co2 = Usage (Map.unionWith (<>) tm1 tm2) (Map.unionWith (<>) co1 co2)

instance Monoid Usage where
  mempty = Usage Map.empty Map.empty

oneTmUse :: TmVar -> Usage
oneTmUse x = Usage (Map.singleton x UsedOnce) Map.empty

oneCoUse :: CoVar -> Usage
oneCoUse k = Usage Map.empty (Map.singleton k UsedOnce)

bindCoUses :: [CoVar] -> Usage -> Usage
bindCoUses ks usage = foldr bindCoUse usage ks

bindCoUse :: CoVar -> Usage -> Usage
bindCoUse k (Usage tms cos) = Usage tms (Map.delete k cos)

bindTmUses :: [TmVar] -> Usage -> Usage
bindTmUses xs usage = foldr bindTmUse usage xs

bindTmUse :: TmVar -> Usage -> Usage
bindTmUse x (Usage tms cos) = Usage (Map.delete x tms) cos

-- lookupTmUsage :: TmVar -> Usage -> Use
-- lookupTmUsage x (Usage tms _) = maybe NeverUsed id (Map.lookup x tms)

lookupCoUsage :: CoVar -> Usage -> Use
lookupCoUsage k (Usage _ cos) = maybe NeverUsed id (Map.lookup k cos)


class CountUses a where
  countUses :: a -> Usage

instance CountUses TermK where
  countUses (HaltK x) = countUses x
  countUses (JumpK k xs) = countUses k <> foldMap countUses xs
  countUses (CallK f xs ks) = countUses f <> foldMap countUses xs <> foldMap countUses ks
  countUses (IfK x k1 k2) = countUses x <> countUses k1 <> countUses k2
  countUses (CaseK x _tcapp alts) = countUses x <> foldMap (countUses . snd) alts
  countUses (LetContK ks e) = foldMap (countUses . snd) ks <> bindCoUses (map fst ks) (countUses e)
  countUses (LetFunK fs e) = foldMap countUses fs <> bindTmUses (map funDefName fs) (countUses e)
  countUses (LetFstK x _t y e) = countUses y <> bindTmUse x (countUses e)
  countUses (LetSndK x _t y e) = countUses y <> bindTmUse x (countUses e)
  countUses (LetFieldK x _t y _f e) = countUses y <> bindTmUse x (countUses e)
  countUses (LetValK x _t v e) = countUses v <> bindTmUse x (countUses e)
  countUses (LetArithK x op e) = countUses op <> bindTmUse x (countUses e)
  countUses (LetCompareK x op e) = countUses op <> bindTmUse x (countUses e)
  countUses (LetStringOpK x _t op e) = countUses op <> bindTmUse x (countUses e)
  countUses (LetBindK x y op e) = countUses op <> bindTmUse x (bindTmUse y (countUses e))

instance CountUses ValueK where
  countUses (VarValK x) = oneTmUse x
  countUses NilValK = mempty
  countUses TokenValK = mempty
  countUses (IntValK _) = mempty
  countUses (CharValK _) = mempty
  countUses (BoolValK _) = mempty
  countUses (StringValK _) = mempty
  countUses (PairValK x y) = countUses x <> countUses y
  countUses (RecordValK fs) = foldMap (countUses . snd) fs
  countUses (CtorValK _c _ts xs) = foldMap countUses xs

instance CountUses ArithK where
  countUses (AddK x y) = countUses x <> countUses y
  countUses (SubK x y) = countUses x <> countUses y
  countUses (MulK x y) = countUses x <> countUses y
  countUses (NegK x) = countUses x

instance CountUses CmpK where
  countUses (CmpEqK x y) = countUses x <> countUses y
  countUses (CmpNeK x y) = countUses x <> countUses y
  countUses (CmpLtK x y) = countUses x <> countUses y
  countUses (CmpLeK x y) = countUses x <> countUses y
  countUses (CmpGtK x y) = countUses x <> countUses y
  countUses (CmpGeK x y) = countUses x <> countUses y
  countUses (CmpEqCharK x y) = countUses x <> countUses y

instance CountUses StringOpK where
  countUses (ConcatK x y) = countUses x <> countUses y
  countUses (IndexK x y) = countUses x <> countUses y
  countUses (LengthK x) = countUses x

instance CountUses PrimIO where
  countUses (PrimGetLine x) = countUses x
  countUses (PrimPutLine x y) = countUses x <> countUses y

instance CountUses Argument where
  countUses (ValueArg x) = countUses x
  countUses (TypeArg _t) = mempty

instance CountUses CoValueK where
  countUses (CoVarK k) = oneCoUse k
  countUses (ContValK cont) = countUses cont

instance CountUses ContDef where
  countUses (ContDef xs e) = bindTmUses (map fst xs) (countUses e)

instance CountUses FunDef where
  countUses (FunDef f xs ks e) =
    bindTmUse f (bindCoUses (map fst ks) (bindTmUses xs' (countUses e)))
    where
      xs' = [x | ValueParam x _ <- xs] -- don't need to worry about type parameters


-- assume that parameters and arguments have same length.
makeJumpSubst :: [(TmVar, TypeK)] -> [ValueK] -> Sub
makeJumpSubst params args = emptySub { subTms = sub, scopeTms = sc }
  where
    sub = Map.fromList (zipWith (\ (x, _t) v -> (x, v)) params args)
    sc = foldMap valueFV args

valueFV :: ValueK -> Set TmVar
valueFV (VarValK x) = Set.singleton x
valueFV NilValK = mempty
valueFV TokenValK = mempty
valueFV (IntValK _) = mempty
valueFV (BoolValK _) = mempty
valueFV (StringValK _) = mempty
valueFV (CharValK _) = mempty
valueFV (PairValK x y) = valueFV x <> valueFV y
valueFV (RecordValK fs) = foldMap (valueFV . snd) fs
valueFV (CtorValK _c _ts xs) = foldMap valueFV xs



-- TODO: Move substitution machinery back into CPS.IR
-- (Well, maybe. It certainly works for type substs, but is it general enough
-- for tm and co substs?)

data Sub
  = Sub {
    subTms :: Map TmVar ValueK -- TODO: Generalize to TmVar :-> ValueK, CoVar :-> CoValueK
  , scopeTms :: Set TmVar
  , subCos :: Map CoVar CoVar
  , scopeCos :: Set CoVar
  , subTys :: Map TyVar TypeK
  , scopeTys :: Set TyVar
  }

emptySub :: Sub
emptySub = Sub { subTms = Map.empty, scopeTms = Set.empty, subCos = Map.empty, scopeCos = Set.empty, subTys = Map.empty, scopeTys = Set.empty }

substTmVar :: Sub -> TmVar -> ValueK
substTmVar sub x = case Map.lookup x (subTms sub) of
  Nothing -> VarValK x
  Just y -> y

substCoVar :: Sub -> CoVar -> CoVar
substCoVar sub x = case Map.lookup x (subCos sub) of
  Nothing -> x
  Just y -> y

substTyVar :: Sub -> TyVar -> TypeK
substTyVar sub aa = case Map.lookup aa (subTys sub) of
  Nothing -> TyVarOccK aa
  Just t -> t

underTm :: Sub -> TmVar -> (TmVar, Sub)
underTm sub x =
  if Set.member x (scopeTms sub) then
    let x' = go (prime x) in
    (x', sub { subTms = Map.insert x (VarValK x') (subTms sub), scopeTms = Set.insert x' (scopeTms sub) })
  else
    (x, sub { subTms = Map.delete x (subTms sub), scopeTms = Set.insert x (scopeTms sub) })
  where
    prime (TmVar v i) = TmVar v (i+1)
    go x' = if Set.member x' (scopeTms sub) then go (prime x') else x'

underTms :: Traversable t => Sub -> t TmVar -> (t TmVar, Sub)
underTms sub xs = let (sub', xs') = mapAccumL f sub xs in (xs', sub')
  where
    f s x = let (x', s') = underTm s x in (s', x')

underCo :: Sub -> CoVar -> (CoVar, Sub)
underCo sub x =
  if Set.member x (scopeCos sub) then
    let x' = go (prime x) in
    (x', sub { subCos = Map.insert x x' (subCos sub), scopeCos = Set.insert x' (scopeCos sub) })
  else
    (x, sub { subCos = Map.delete x (subCos sub), scopeCos = Set.insert x (scopeCos sub) })
  where
    prime (CoVar v i) = CoVar v (i+1)
    go x' = if Set.member x' (scopeCos sub) then go (prime x') else x'

underCos :: Traversable t => Sub -> t CoVar -> (t CoVar, Sub)
underCos sub xs = let (sub', xs') = mapAccumL f sub xs in (xs', sub')
  where
    f s x = let (x', s') = underCo s x in (s', x')

underContParams :: Sub -> [(TmVar, TypeK)] -> ([(TmVar, TypeK)], Sub)
underContParams sub [] = ([], sub)
underContParams sub ((x, t) : xs) =
  let (x', sub') = underTm sub x in
  let (xs', sub'') = underContParams sub' xs in
  ((x', subst sub t) : xs', sub'')

underTy :: Sub -> TyVar -> (TyVar, Sub)
underTy sub x =
  if Set.member x (scopeTys sub) then
    let x' = go (prime x) in
    (x', sub { subTys = Map.insert x (TyVarOccK x') (subTys sub), scopeTys = Set.insert x' (scopeTys sub) })
  else
    (x, sub { subTys = Map.delete x (subTys sub), scopeTys = Set.insert x (scopeTys sub) })
  where
    prime (TyVar v i) = TyVar v (i+1)
    go x' = if Set.member x' (scopeTys sub) then go (prime x') else x'


-- a group of recursive bindings can be thought of as a collection of
-- declarations/binders, followed by a collection of assignments/definitions to those
-- binders.
--
-- This function passes a substitution under the declarations, producing an
-- extend substitution to apply to each of the assignments/definitions and the
-- body.
underRecFunDecls :: Sub -> [FunDef] -> Sub
underRecFunDecls sub fs = let (_fs', sub') = underTms sub (map funDefName fs) in sub'

underFunParams :: Sub -> [FunParam] -> ([FunParam], Sub)
underFunParams sub [] = ([], sub)
underFunParams sub (ValueParam x t : xs) =
  let (x', sub') = underTm sub x in
  let (xs', sub'') = underFunParams sub' xs in
  (ValueParam x' (subst sub t) : xs', sub'')
underFunParams sub (TypeParam aa k : xs) =
  let (aa', sub') = underTy sub aa in
  let (xs', sub'') = underFunParams sub' xs in
  (TypeParam aa' k : xs', sub'')

underFunCoParams :: Sub -> [(CoVar, CoTypeK)] -> ([(CoVar, CoTypeK)], Sub)
underFunCoParams sub [] = ([], sub)
underFunCoParams sub ((k, s) : ks) =
  let (k', sub') = underCo sub k in
  let (ks', sub'') = underFunCoParams sub' ks in
  ((k', subst sub s) : ks', sub'')

underFunTele :: Sub -> [TeleEntry] -> ([TeleEntry], Sub)
underFunTele sub [] = ([], sub)
underFunTele sub (ValueTele t : tele) =
  let (tele', sub') = underFunTele sub tele in
  (ValueTele (subst sub t) : tele', sub')
underFunTele sub (TypeTele aa k : tele) =
  let (aa', sub') = underTy sub aa in
  let (tele', sub'') = underFunTele sub' tele in
  (TypeTele aa' k : tele', sub'')

class Subst a where
  subst :: Sub -> a -> a

instance Subst TermK where
  subst sub (HaltK x) = HaltK (subst sub x)
  subst sub (JumpK k xs) = JumpK (subst sub k) (map (subst sub) xs)
  subst sub (CallK f xs ks) = CallK (subst sub f) (map (subst sub) xs) (map (subst sub) ks)
  subst sub (IfK x k1 k2) = IfK (subst sub x) (subst sub k1) (subst sub k2)
  subst sub (CaseK x tcapp alts) = CaseK (subst sub x) (subst sub tcapp) (map (second (subst sub)) alts)
  subst sub (LetContK ks e) =
    let conts' = map (subst sub . snd) ks in
    let (ks', sub') = underCos sub (map fst ks) in
    LetContK (zip ks' conts') (subst sub' e)
  subst sub (LetFunK fs e) =
    let sub' = underRecFunDecls sub fs in
    let fs' = map (subst sub') fs in
    let e' = subst sub' e in
    LetFunK fs' e'
  subst sub (LetValK x t v e) =
    let (x', sub') = underTm sub x in
    LetValK x' (subst sub t) (subst sub v) (subst sub' e)
  subst sub (LetFstK x t y e) =
    let (x', sub') = underTm sub x in
    LetFstK x' (subst sub t) (subst sub y) (subst sub' e)
  subst sub (LetSndK x t y e) =
    let (x', sub') = underTm sub x in
    LetSndK x' (subst sub t) (subst sub y) (subst sub' e)
  subst sub (LetFieldK x t y f e) =
    let (x', sub') = underTm sub x in
    LetFieldK x' (subst sub t) (subst sub y) f (subst sub' e)
  subst sub (LetArithK x op e) =
    let (x', sub') = underTm sub x in
    LetArithK x' (subst sub op) (subst sub' e)
  subst sub (LetCompareK x op e) =
    let (x', sub') = underTm sub x in
    LetCompareK x' (subst sub op) (subst sub' e)
  subst sub (LetStringOpK x t op e) =
    let (x', sub') = underTm sub x in
    LetStringOpK x' (subst sub t) (subst sub op) (subst sub' e)
  subst sub (LetBindK x y op e) =
    let (x', sub') = underTm sub x in
    let (y', sub'') = underTm sub' y in
    LetBindK x' y' (subst sub op) (subst sub'' e)

instance Subst Argument where
  subst sub (ValueArg x) = ValueArg (subst sub x)
  subst sub (TypeArg t) = TypeArg (subst sub t)

instance Subst ValueK where
  subst sub (VarValK x) = substTmVar sub x
  subst _ NilValK = NilValK
  subst _ TokenValK = TokenValK
  subst _ (IntValK i) = IntValK i
  subst _ (BoolValK b) = BoolValK b
  subst _ (StringValK s) = StringValK s
  subst _ (CharValK c) = CharValK c
  subst sub (RecordValK fs) = RecordValK (map (second (subst sub)) fs)
  subst sub (CtorValK c ts xs) = CtorValK c (map (subst sub) ts) (map (subst sub) xs)
  subst sub (PairValK x y) = PairValK (subst sub x) (subst sub y)

instance Subst CoValueK where
  subst sub (CoVarK k) = CoVarK (substCoVar sub k)
  subst sub (ContValK cont) = ContValK (subst sub cont)

instance Subst ArithK where
  subst sub (AddK x y) = AddK (subst sub x) (subst sub y)
  subst sub (SubK x y) = SubK (subst sub x) (subst sub y)
  subst sub (MulK x y) = MulK (subst sub x) (subst sub y)
  subst sub (NegK x) = NegK (subst sub x)

instance Subst CmpK where
  subst sub (CmpEqK x y) = CmpEqK (subst sub x) (subst sub y)
  subst sub (CmpNeK x y) = CmpNeK (subst sub x) (subst sub y)
  subst sub (CmpLtK x y) = CmpLtK (subst sub x) (subst sub y)
  subst sub (CmpLeK x y) = CmpLeK (subst sub x) (subst sub y)
  subst sub (CmpGtK x y) = CmpGtK (subst sub x) (subst sub y)
  subst sub (CmpGeK x y) = CmpGeK (subst sub x) (subst sub y)
  subst sub (CmpEqCharK x y) = CmpEqCharK (subst sub x) (subst sub y)

instance Subst StringOpK where
  subst sub (ConcatK x y) = ConcatK (subst sub x) (subst sub y)
  subst sub (IndexK x y) = IndexK (subst sub x) (subst sub y)
  subst sub (LengthK x) = LengthK (subst sub x)

instance Subst PrimIO where
  subst sub (PrimGetLine x) = PrimGetLine (subst sub x)
  subst sub (PrimPutLine x y) = PrimPutLine (subst sub x) (subst sub y)

instance Subst ContDef where
  subst sub (ContDef xs e) =
    let (xs', sub') = underContParams sub xs in
    ContDef xs' (subst sub' e)

instance Subst FunDef where
  subst sub (FunDef f xs ks e) =
    let (xs', sub') = underFunParams sub xs in
    let (ks', sub'') = underFunCoParams sub' ks in
    -- Ugh. this should only ever be a renaming, but unfortunately I can only
    -- express substitution.
    let VarValK f' = substTmVar sub f in
    FunDef f' xs' ks' (subst sub'' e)

instance Subst TypeK where
  subst sub (TyVarOccK aa) = substTyVar sub aa
  subst sub (FunK tele ss) =
    let (tele', sub') = underFunTele sub tele in
    FunK tele' (map (subst sub') ss)
  subst _ UnitK = UnitK
  subst _ IntK = IntK
  subst _ BoolK = BoolK
  subst _ StringK = StringK
  subst _ CharK = CharK
  subst _ TokenK = TokenK
  subst _ (TyConOccK tc) = TyConOccK tc
  subst sub (ProdK t s) = ProdK (subst sub t) (subst sub s)
  subst sub (TyAppK t s) = TyAppK (subst sub t) (subst sub s)
  subst sub (RecordK fs) = RecordK (map (second (subst sub)) fs)

instance Subst CoTypeK where
  subst sub (ContK ts) = ContK (map (subst sub) ts)

instance Subst TyConApp where
  subst sub (TyConApp tc ts) = TyConApp tc (map (subst sub) ts)


