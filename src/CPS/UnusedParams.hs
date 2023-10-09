
module CPS.UnusedParams (dropUnusedParams) where

import CPS.IR

import Control.Monad.Reader hiding (join)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (catMaybes)
import Data.Traversable (for)
import Prelude hiding (cos)

-- A pass that removes unused parameters from ContDefs and FunDefs,
-- transforming call sites to match.
--
-- It does not affect unused value bindings, but maybe it should.
-- (Likewise, it does not discard unused fun or cont bindings. It only affects
-- parameter lists and call sites.)
-- An interesting potential follow-up: contification of zero-cont functions.
-- (not to be confused with the other form of contification, which uses
-- CFA-lite to determine that only one continuation flows to a particular
-- function, and so fuses that continuation into the function definition)

-- Note: Unique variable binders. It seems increasingly clear that many
-- optimization passes would benefit from attaching a unique identifier/integer
-- to every variable binder in a program.
--
-- THe primary benefit of this is that it allows me to use side tables to store
-- the results of an analysis pass. (Alternately, I could parametrize the IR by
-- a type for annotations, but that turned out to be a lot of boilerplate for
-- not much practical use, and my previous impl of this was limited to noly
-- function/cont annotations, not annotations on ordinary binders as well.)

dropUnusedParams :: Program -> Program
dropUnusedParams (Program ds e) = runM $ do
  (e', _) <- dropUnusedTerm e
  pure (Program ds e')


dropUnusedTerm :: TermK -> M (TermK, AllUsage)
dropUnusedTerm (HaltK x) = pure (HaltK x, useTmVar x)
dropUnusedTerm (JumpK k xs) = transformJumpSite k xs
dropUnusedTerm (CallK f xs ks) = transformCallSite f xs ks
dropUnusedTerm (LetContK ks e) = do
  (ks', tfs, usages) <- fmap unzip3 $ for ks $ \ (k, contDef) -> do
    let wk = isWellKnownTerm k e
    (contDef', usage, mtf) <- transformContDef' wk contDef
    pure ((k, contDef'), (,) k <$> mtf, usage)
  (e', usage') <- withJumpSiteTransformers (catMaybes tfs) $ dropUnusedTerm e
  pure (LetContK ks' e', mconcat usages <> usage')
dropUnusedTerm (LetFunK fs e) = do
  (fs', tfs, usages) <- fmap unzip3 $ for fs $ \funDef -> do
    let f = funDefName funDef
    let wk = NotWellKnown -- TODO: check for occurrences in 'e' as well as in any of the fs
    (funDef', usage, mtf) <- transformFunDef' wk funDef
    pure (funDef', (,) f <$> mtf, usage)
  (e', usage') <- withCallSiteTransformers (catMaybes tfs) $ dropUnusedTerm e
  pure (LetFunK fs' e', mconcat usages <> usage')
dropUnusedTerm (IfK x kt kf) = do
  (kt', ktusage) <- transformContDef kt
  (kf', kfusage) <- transformContDef kf
  pure (IfK x kt' kf', useTmVar x <> ktusage <> kfusage)
dropUnusedTerm (CaseK x tcapp alts) = do
  (alts', usages) <- fmap unzip $ for alts $ \ (c, coval) -> do
    (coval', usage) <- transformCoValue coval
    pure ((c, coval'), usage)
  pure (CaseK x tcapp alts', useTmVar x <> mconcat usages)

-- Other cases basically just recurse.
dropUnusedTerm (LetValK x t v e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetValK x t v e', typeUsage t <> valueUsage v <> bindTmUsage x usage)
dropUnusedTerm (LetArithK x op e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetArithK x op e', arithUsage op <> bindTmUsage x usage)
dropUnusedTerm (LetCompareK x op e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetCompareK x op e', cmpUsage op <> bindTmUsage x usage)
dropUnusedTerm (LetStringOpK x t op e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetStringOpK x t op e', stringOpUsage op <> typeUsage t <> bindTmUsage x usage)
dropUnusedTerm (LetFstK x t y e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetFstK x t y e', useTmVar y <> bindTmUsage x usage)
dropUnusedTerm (LetSndK x t y e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetSndK x t y e', useTmVar y <> bindTmUsage x usage)
dropUnusedTerm (LetFieldK x t y f e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetFieldK x t y f e', useTmVar y <> bindTmUsage x usage)
dropUnusedTerm (LetBindK x y op e) = do
  (e', usage) <- dropUnusedTerm e
  pure (LetBindK x y op e', primIOUsage op <> bindTmUsage x (bindTmUsage y usage))

transformContDef' :: IsWellKnown -> ContDef -> M (ContDef, AllUsage, Maybe JumpSiteTransformer)
transformContDef' wk (ContDef xs e) = do
  (e', usage) <- dropUnusedTerm e
  if wk <= WellKnown then do
    let (xs', usage', tf) = restrictContValueParams xs usage
    pure (ContDef xs' e', usage', Just (JST tf))
  else do
    let usage' = go xs usage
    pure (ContDef xs e', usage', Nothing)
    where
      go [] acc = acc
      go ((x, t) : xs') acc = typeUsage t <> bindTmUsage x (go xs' acc)

transformFunDef' :: IsWellKnown -> FunDef -> M (FunDef, AllUsage, Maybe CallSiteTransformer)
transformFunDef' wk (FunDef f xs ks e) = do
  (e', usage) <- dropUnusedTerm e
  if wk <= WellKnown then do
    let (ks', usage', ktf) = restrictFunCoParams ks usage
    let (xs', usage'', xtf) = restrictFunValueParams xs usage'
    pure (FunDef f xs' ks' e', usage'', Just (CST xtf ktf))
  else do
    let usage' = go2 xs (go1 ks usage)
    pure (FunDef f xs ks e', usage', Nothing)
    where
      go1 [] acc = acc
      go1 ((k, s) : ks') acc = coTypeUsage s <> bindCoUsage k (go1 ks' acc)
      go2 [] acc = acc
      go2 (ValueParam x t : xs') acc = typeUsage t <> bindTmUsage x (go2 xs' acc)
      go2 (TypeParam aa _k : xs') acc = bindTyUsage aa (go2 xs' acc)

transformJumpSite :: CoVar -> [TmVar] -> M (TermK, AllUsage)
transformJumpSite k xs = do
  (Map.lookup k <$> asks jumpTFs) >>= \case
    Nothing -> pure (JumpK k xs, useCoVar k <> foldMap useTmVar xs)
    Just (JST tf) -> do
      let (xs', xusages) = unzip (go tf xs)
      pure (JumpK k xs', useCoVar k <> mconcat xusages)
  where
    go NoArgs [] = []
    go (KeepArg tf') (y : ys) = (y, useTmVar y) : go tf' ys
    go (DropArg tf') (_y : ys) = go tf' ys
    go _ _ = error "bad: jump site doesn't match pattern"

transformCallSite :: TmVar -> [Argument] -> [CoValueK] -> M (TermK, AllUsage)
transformCallSite f xs ks = do
  (Map.lookup f <$> asks callTFs) >>= \case
    Nothing -> do
      (ks', kusages) <- fmap unzip $ traverse transformCoValue ks
      pure (CallK f xs ks', useTmVar f <> foldMap argumentUsage xs <> mconcat kusages)
    Just (CST xtf ktf) -> do
      let (xs', xusages) = unzip (go1 xtf xs)
      (ks', kusages) <- fmap unzip $ go2 ktf ks
      pure (CallK f xs' ks', useTmVar f <> mconcat xusages <> mconcat kusages)
  where
    go1 NoArgs [] = []
    go1 (KeepArg tf') (arg : args) = (arg, argumentUsage arg) : go1 tf' args
    go1 (DropArg tf') (_arg : args) = go1 tf' args
    go1 _ _ = error "bad: call site doesn't match pattern"

    go2 NoArgs [] = pure []
    go2 (KeepArg tf') (coarg : coargs) = (:) <$> transformCoValue coarg <*> go2 tf' coargs
    go2 (DropArg tf') (_coarg : coargs) = go2 tf' coargs
    go2 _ _ = error "bad: call co-site doesn't match pattern"


newtype JumpSiteTransformer = JST ArgsTransformer

data CallSiteTransformer = CST ArgsTransformer ArgsTransformer

-- maybe instead of NoArgs have KeepAllRemainingArgs? eh, not really that useful.
data ArgsTransformer = NoArgs | KeepArg ArgsTransformer | DropArg ArgsTransformer

restrictContValueParams :: [(TmVar, TypeK)] -> AllUsage -> ([(TmVar, TypeK)], AllUsage, ArgsTransformer)
restrictContValueParams [] usage = ([], usage, NoArgs)
restrictContValueParams ((x, t) : xs) usage =
    let (xs', usage', tf) = restrictContValueParams xs usage in
    case lookupTmUsage x usage' of
      Unused -> (xs', bindTmUsage x usage', DropArg tf)
      MaybeUsed -> ((x, t) : xs', typeUsage t <> bindTmUsage x usage', KeepArg tf)

restrictFunCoParams :: [(CoVar, CoTypeK)] -> AllUsage -> ([(CoVar, CoTypeK)], AllUsage, ArgsTransformer)
restrictFunCoParams [] usage = ([], usage, NoArgs)
restrictFunCoParams ((k, s) : ks) usage =
  let (ks', usage', tf) = restrictFunCoParams ks usage in
  case lookupCoUsage k usage' of
    Unused -> (ks', bindCoUsage k usage', DropArg tf)
    MaybeUsed -> ((k, s) : ks', coTypeUsage s <> bindCoUsage k usage', KeepArg tf)

restrictFunValueParams :: [FunParam] -> AllUsage -> ([FunParam], AllUsage, ArgsTransformer)
restrictFunValueParams [] usage = ([], usage, NoArgs)
restrictFunValueParams (ValueParam x t : xs) usage =
  let (xs', usage', tf) = restrictFunValueParams xs usage in
  case lookupTmUsage x usage' of
    Unused -> (xs', bindTmUsage x usage', DropArg tf)
    MaybeUsed -> (ValueParam x t : xs', typeUsage t <> bindTmUsage x usage', KeepArg tf)
restrictFunValueParams (TypeParam aa k : xs) usage =
  let (xs', usage', tf) = restrictFunValueParams xs usage in
  case lookupTyUsage aa usage' of
    Unused -> (xs', bindTyUsage aa usage', DropArg tf)
    MaybeUsed -> (TypeParam aa k : xs', bindTyUsage aa usage', KeepArg tf)


transformCoValue :: CoValueK -> M (CoValueK, AllUsage)
transformCoValue (CoVarK k) = pure (CoVarK k, useCoVar k)
transformCoValue (ContValK cont) = do
  (cont', usage) <- transformContDef cont -- transformContDef' NotWellKnown cont
  pure (ContValK cont', usage)

-- Note: Does not remove unused parameters.
-- This is because we cannot statically know the call sites of this
-- continuation without signficant effort (i.e., CFA-style whole-program
-- analysis)
--
-- However, we can still transform the body.
transformContDef :: ContDef -> M (ContDef, AllUsage)
transformContDef (ContDef xs e) = do
  (e', usage) <- dropUnusedTerm e
  let usage' = go xs usage
  pure (ContDef xs e', usage')
  where
    go [] acc = acc
    go ((x, t) : xs') acc = typeUsage t <> bindTmUsage x (go xs' acc)


newtype M a = M { getM :: Reader Env a }

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader Env M

data Env = Env { jumpTFs :: Map CoVar JumpSiteTransformer, callTFs :: Map TmVar CallSiteTransformer }

emptyEnv :: Env
emptyEnv = Env { jumpTFs = Map.empty, callTFs = Map.empty }

runM :: M a -> a
runM m = flip runReader emptyEnv $ getM m

insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

withCallSiteTransformers :: [(TmVar, CallSiteTransformer)] -> M a -> M a
withCallSiteTransformers tfs m = local extend m
  where extend env = env { callTFs = insertMany tfs (callTFs env) }

withJumpSiteTransformers :: [(CoVar, JumpSiteTransformer)] -> M a -> M a
withJumpSiteTransformers tfs m = local extend m
  where extend env = env { jumpTFs = insertMany tfs (jumpTFs env) }



type TmVarUsage = Map TmVar Usage
type CoVarUsage = Map CoVar Usage
type TyVarUsage = Map TyVar Usage
data AllUsage = AllUsage TmVarUsage CoVarUsage TyVarUsage
instance Semigroup AllUsage where
  AllUsage tm1 co1 ty1 <> AllUsage tm2 co2 ty2 =
    AllUsage (Map.unionWith join tm1 tm2) (Map.unionWith join co1 co2) (Map.unionWith join ty1 ty2)
instance Monoid AllUsage where
  mempty = AllUsage mempty mempty mempty

data Usage = Unused | MaybeUsed

join :: Usage -> Usage -> Usage
join Unused Unused = Unused -- 'Unused' is bottom element
join Unused MaybeUsed = MaybeUsed
join MaybeUsed Unused = MaybeUsed
join MaybeUsed MaybeUsed = MaybeUsed

useTmVar :: TmVar -> AllUsage
useTmVar x = AllUsage (Map.singleton x MaybeUsed) mempty mempty

useCoVar :: CoVar -> AllUsage
useCoVar k = AllUsage mempty (Map.singleton k MaybeUsed) mempty

useTyVar :: TyVar -> AllUsage
useTyVar aa = AllUsage mempty mempty (Map.singleton aa MaybeUsed)

lookupTmUsage :: TmVar -> AllUsage -> Usage
lookupTmUsage x (AllUsage tms _ _) = maybe Unused id (Map.lookup x tms)

lookupCoUsage :: CoVar -> AllUsage -> Usage
lookupCoUsage k (AllUsage _ cos _) = maybe Unused id (Map.lookup k cos)

lookupTyUsage :: TyVar -> AllUsage -> Usage
lookupTyUsage aa (AllUsage _ _ tys) = maybe Unused id (Map.lookup aa tys)

bindTmUsage :: TmVar -> AllUsage -> AllUsage
bindTmUsage x (AllUsage tms cos tys) = AllUsage (Map.delete x tms) cos tys

bindCoUsage :: CoVar -> AllUsage -> AllUsage
bindCoUsage k (AllUsage tms cos tys) = AllUsage tms (Map.delete k cos) tys

bindTyUsage :: TyVar -> AllUsage -> AllUsage
bindTyUsage aa (AllUsage tms cos tys) = AllUsage tms cos (Map.delete aa tys)


argumentUsage :: Argument -> AllUsage
argumentUsage (ValueArg x) = useTmVar x
argumentUsage (TypeArg t) = typeUsage t

typeUsage :: TypeK -> AllUsage
typeUsage (TyVarOccK aa) = useTyVar aa
typeUsage UnitK = mempty
typeUsage TokenK = mempty
typeUsage IntK = mempty
typeUsage BoolK = mempty
typeUsage StringK = mempty
typeUsage CharK = mempty
typeUsage (TyConOccK _) = mempty
typeUsage (ProdK t1 t2) = typeUsage t1 <> typeUsage t2
typeUsage (TyAppK t1 t2) = typeUsage t1 <> typeUsage t2
typeUsage (RecordK fs) = foldMap (typeUsage . snd) fs
typeUsage (FunK tele ss) = teleUsage tele (foldMap coTypeUsage ss)

teleUsage :: [TeleEntry] -> AllUsage -> AllUsage
teleUsage [] usage = usage
teleUsage (ValueTele t : tele) usage = typeUsage t <> teleUsage tele usage
teleUsage (TypeTele aa _k : tele) usage = bindTyUsage aa (teleUsage tele usage)

coTypeUsage :: CoTypeK -> AllUsage
coTypeUsage (ContK ts) = foldMap typeUsage ts

valueUsage :: ValueK -> AllUsage
valueUsage (PairK x y) = useTmVar x <> useTmVar y
valueUsage (RecordValK fs) = foldMap (useTmVar . snd) fs
valueUsage (CtorAppK _c _ts xs) = foldMap useTmVar xs
valueUsage NilK = mempty
valueUsage WorldTokenK = mempty
valueUsage (IntValK _) = mempty
valueUsage (BoolValK _) = mempty
valueUsage (StringValK _) = mempty
valueUsage (CharValK _) = mempty

arithUsage :: ArithK -> AllUsage
arithUsage (AddK x y) = useTmVar x <> useTmVar y
arithUsage (SubK x y) = useTmVar x <> useTmVar y
arithUsage (MulK x y) = useTmVar x <> useTmVar y
arithUsage (NegK x) = useTmVar x

cmpUsage :: CmpK -> AllUsage
cmpUsage (CmpEqK x y) = useTmVar x <> useTmVar y
cmpUsage (CmpNeK x y) = useTmVar x <> useTmVar y
cmpUsage (CmpLtK x y) = useTmVar x <> useTmVar y
cmpUsage (CmpLeK x y) = useTmVar x <> useTmVar y
cmpUsage (CmpGtK x y) = useTmVar x <> useTmVar y
cmpUsage (CmpGeK x y) = useTmVar x <> useTmVar y
cmpUsage (CmpEqCharK x y) = useTmVar x <> useTmVar y

stringOpUsage :: StringOpK -> AllUsage
stringOpUsage (ConcatK x y) = useTmVar x <> useTmVar y
stringOpUsage (IndexK x y) = useTmVar x <> useTmVar y
stringOpUsage (LengthK x) = useTmVar x

primIOUsage :: PrimIO -> AllUsage
primIOUsage (PrimGetLine s) = useTmVar s
primIOUsage (PrimPutLine s x) = useTmVar s <> useTmVar x


-- IsWellKnown is the three-point lattice bot <= well-known <= top
-- - bot represents a function that is never called. arbitrary properties can be
--   assumed about its callsites
-- - well-known represents a function whose call sites are all statically known
--   (e.g., it is never used in a higher-order manner)
-- - top represents any function. No properties can be assumed about its
--   callsites.
data IsWellKnown = NeverCalled | WellKnown | NotWellKnown
  deriving (Eq, Ord)
  -- Strictly speaking, Ord should be defined in terms of the lattice operation
  -- (that is, 'x <= y <==> (x \/ y) == y'), but autoderive gives an equivalent
  -- implementation.

-- the lattice join of two IsWellKnown values.
instance Semigroup IsWellKnown where
  NeverCalled <> x = x
  x <> NeverCalled = x
  WellKnown <> WellKnown = WellKnown
  WellKnown <> NotWellKnown = NotWellKnown
  NotWellKnown <> WellKnown = NotWellKnown
  NotWellKnown <> NotWellKnown = NotWellKnown

instance Monoid IsWellKnown where
  mempty = WellKnown

-- | Check that a covar is well-known within a term.
isWellKnownTerm :: CoVar -> TermK -> IsWellKnown
-- Block terminators
isWellKnownTerm _k (HaltK _x) = NeverCalled
isWellKnownTerm k (JumpK k' _xs) = if k == k' then WellKnown else NeverCalled
isWellKnownTerm k (CallK _f _xs ks) = go ks
  where
    go [] = NeverCalled
    go (co : ks') = isWellKnownCoVal k co <> go ks'
isWellKnownTerm k (IfK _x k1 k2) = isWellKnownCont k k1 <> isWellKnownCont k k2
isWellKnownTerm k (CaseK _x _tcapp alts) = go alts
  where
    go [] = NeverCalled
    go ((_c, co) : alts') = isWellKnownCoVal k co <> go alts'
-- function/continuation definitions
isWellKnownTerm k (LetContK ks e) =
  go ks <> if any (\ (k', _) -> k == k') ks then NeverCalled else isWellKnownTerm k e
  where
    go [] = NeverCalled
    go ((_k', cont) : ks') = isWellKnownCont k cont <> go ks'
isWellKnownTerm k (LetFunK fs e) = go fs <> isWellKnownTerm k e
  where
    go [] = NeverCalled
    go (fun : fs') = isWellKnownFunDef k fun <> go fs'
-- easy cases
isWellKnownTerm k (LetValK _x _t _v e) = isWellKnownTerm k e
isWellKnownTerm k (LetFstK _x _t _y e) = isWellKnownTerm k e
isWellKnownTerm k (LetSndK _x _t _y e) = isWellKnownTerm k e
isWellKnownTerm k (LetFieldK _x _t _y _f e) = isWellKnownTerm k e
isWellKnownTerm k (LetArithK _x _op e) = isWellKnownTerm k e
isWellKnownTerm k (LetCompareK _x _op e) = isWellKnownTerm k e
isWellKnownTerm k (LetStringOpK _x _t _op e) = isWellKnownTerm k e
isWellKnownTerm k (LetBindK _x _y _op e) = isWellKnownTerm k e

isWellKnownCoVal :: CoVar -> CoValueK -> IsWellKnown
isWellKnownCoVal k (CoVarK k') = if k == k' then NotWellKnown else NeverCalled
isWellKnownCoVal k (ContValK cont) = isWellKnownCont k cont

isWellKnownCont :: CoVar -> ContDef -> IsWellKnown
isWellKnownCont k (ContDef _xs e) = isWellKnownTerm k e -- tmvar paramlist cannot capture k.

isWellKnownFunDef :: CoVar -> FunDef -> IsWellKnown
isWellKnownFunDef k (FunDef _f _xs ks e) = if any (\ (k', _s) -> k == k') ks then NeverCalled else isWellKnownTerm k e

