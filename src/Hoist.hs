{-# LANGUAGE
    StandaloneDeriving
  , DerivingStrategies
  , GeneralizedNewtypeDeriving
  , MultiParamTypeClasses
  , FlexibleInstances
  #-}

-- | Hoisting serves two purposes: to split local closure definitions into
-- top-level code declarations and local closure allocations, and to associate
-- pass around type info values, when needed.
--
-- Perhaps the latter task might be better suited to another pass. Hmm.
module Hoist
    ( hoistProgram
    , pprintProgram
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)
import Control.Monad.State

import Data.Traversable (for, mapAccumL)

import qualified CC.IR as C

import Hoist.IR hiding (Scope, emptyScope, Subst, singleSubst, substSort)


-- Note: Part of the confusion between type places and info places is that when
-- translating from CC to Hoist, a CC type variable binding becomes an (erased)
-- type variable binding and a (relevant) info binding.
--
-- At least, that's how I think it should be. So far, I've been turning tyvar
-- binds into info bindings and ignoring the hoist-level tyvar bindings,
-- because they do not impact code generation. The type-checker, however, cares
-- more.

asPlace :: C.Sort -> C.Name -> Place
asPlace s (C.Name x i) = Place (sortOf s) (Id (x ++ show i))

asInfoPlace :: C.TyVar -> InfoPlace
asInfoPlace (C.TyVar aa) = InfoPlace (Id aa)

-- TODO: Be principled about CC.TyVar <-> Hoist.TyVar conversions
asTyVar :: C.TyVar -> TyVar
asTyVar (C.TyVar aa) = TyVar aa

asClosureName :: C.Name -> ClosureName
asClosureName (C.Name x i) = ClosureName (x ++ show i)

sortOf :: C.Sort -> Sort
sortOf C.Integer = IntegerH
sortOf C.Boolean = BooleanH
sortOf C.Unit = UnitH
sortOf C.Sum = SumH
sortOf C.String = StringH
sortOf (C.Pair t s) = ProductH (sortOf t) (sortOf s)
sortOf (C.List t) = ListH (sortOf t)
sortOf (C.Closure ss) = ClosureH (ClosureTele (map f ss))
  where
    f (C.ValueTele s) = ValueTele (sortOf s)
    f (C.TypeTele aa) = TypeTele (asTyVar aa)
sortOf (C.Alloc aa) = AllocH (asTyVar aa)

caseKind :: C.CaseKind -> CaseKind
caseKind C.CaseBool = CaseBool
caseKind (C.CaseSum a b) = CaseSum (sortOf a) (sortOf b)
caseKind (C.CaseList a) = CaseList (sortOf a)



-- Hmm. Instead of 'Writer', would an 'Update' monad be applicable here?
newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set ClosureName) (Writer ClosureDecls)) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter ClosureDecls HoistM
deriving newtype instance MonadState (Set ClosureName) HoistM

data HoistEnv = HoistEnv { localScope :: Scope, envScope :: Scope }

-- Hmm. Why is Scope 'Map C.Name Place', but then 'Map H.TyVar InfoPlace'?
data Scope = Scope { scopePlaces :: Map C.Name Place, scopeInfos :: Map TyVar InfoPlace }

newtype ClosureDecls = ClosureDecls [ClosureDecl]

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls


tellClosures :: [ClosureDecl] -> HoistM ()
tellClosures cs = tell (ClosureDecls cs)


hoistProgram :: C.TermC -> Program
hoistProgram srcC =
  let (srcH, ClosureDecls cs) = runHoist (hoist srcC) in
  Program cs srcH

runHoist :: HoistM a -> (a, ClosureDecls)
runHoist =
  runWriter .
  flip evalStateT Set.empty .
  flip runReaderT emptyEnv .
  runHoistM
  where
    emptyEnv = HoistEnv emptyScope emptyScope
    emptyScope = Scope Map.empty Map.empty


-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
hoist :: C.TermC -> HoistM TermH
hoist (C.HaltC x) = do
  (x', s) <- hoistVarOccSort x
  i <- infoForSort s
  pure (HaltH s x' i)
hoist (C.JumpC k xs) = do
  k' <- hoistVarOcc k
  ys <- hoistArgList xs
  pure (OpenH k' ys)
hoist (C.CallC f xs ks) = do
  f' <- hoistVarOcc f
  ys <- hoistArgList (xs ++ ks)
  pure (OpenH f' ys)
hoist (C.InstC f ts ks) = do
  f' <- hoistVarOcc f
  ys <- hoistArgList ks
  ts' <- traverse (infoForSort . sortOf) ts
  pure (OpenH f' (map TypeArg ts' ++ ys))
hoist (C.CaseC x t ks) = do
  x' <- hoistVarOcc x
  let kind = caseKind t
  ks' <- traverse hoistVarOcc ks
  pure $ CaseH x' kind ks'
hoist (C.LetValC (x, s) v e) = do
  v' <- hoistValue v
  (x', e') <- withPlace x s $ hoist e
  pure $ LetValH x' v' e'
hoist (C.LetFstC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetProjectH x' y' ProjectFst e')
hoist (C.LetSndC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetProjectH x' y' ProjectSnd e')
hoist (C.LetArithC (x, s) op e) = do
  op' <- hoistArith op
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' op' e')
hoist (C.LetNegateC (x, s) y e) = do
  y' <- hoistVarOcc y
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' (PrimNegInt64 y') e')
hoist (C.LetCompareC (x, s) cmp e) = do
  cmp' <- hoistCmp cmp
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' cmp' e')
hoist (C.LetConcatC (x, s) y z e) = do
  y' <- hoistVarOcc y
  z' <- hoistVarOcc z
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' (PrimConcatenate y' z') e')
hoist (C.LetFunC fs e) = do
  fdecls <- declareClosureNames C.funClosureName fs
  ds' <- traverse hoistFunClosure fdecls
  tellClosures ds'
  hoistClosureAllocs C.funClosureName C.funClosureSort C.funEnvDef fdecls e
hoist (C.LetContC ks e) = do
  kdecls <- declareClosureNames C.contClosureName ks
  ds' <- traverse hoistContClosure kdecls
  tellClosures ds'
  hoistClosureAllocs C.contClosureName C.contClosureSort C.contEnvDef kdecls e

hoistFunClosure :: (ClosureName, C.FunClosureDef) -> HoistM ClosureDecl
hoistFunClosure (fdecl, C.FunClosureDef _f env tele body) = do
  inClosure env tele $ \env' params' -> do
    body' <- hoist body
    pure (ClosureDecl fdecl env' params' body')

hoistContClosure :: (ClosureName, C.ContClosureDef) -> HoistM ClosureDecl
hoistContClosure (kdecl, C.ContClosureDef _k env xs body) = do
  let tele = C.makeClosureParams [] xs
  inClosure env tele $ \env' params' -> do
    body' <- hoist body
    pure (ClosureDecl kdecl env' params' body')

hoistValue :: C.ValueC -> HoistM ValueH
hoistValue (C.IntC i) = pure (IntH (fromIntegral i))
hoistValue (C.BoolC b) = pure (BoolH b)
hoistValue (C.PairC x y) =
  (\ (x', i) (y', j) -> PairH i j x' y') <$> hoistVarOccInfo x <*> hoistVarOccInfo y
hoistValue C.NilC = pure NilH
hoistValue (C.InlC x) = (\ (x', i) -> InlH i x') <$> hoistVarOccInfo x
hoistValue (C.InrC x) = (\ (x', i) -> InrH i x') <$> hoistVarOccInfo x
hoistValue C.EmptyC = pure ListNilH
hoistValue (C.ConsC x xs) =
  (\ (x', i) xs' -> ListConsH i x' xs') <$> hoistVarOccInfo x <*> hoistVarOcc xs
hoistValue (C.StringC s) = pure (StringValH s)

hoistArith :: C.ArithC -> HoistM PrimOp
hoistArith (C.AddC x y) = PrimAddInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistArith (C.SubC x y) = PrimSubInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistArith (C.MulC x y) = PrimMulInt64 <$> hoistVarOcc x <*> hoistVarOcc y

hoistCmp :: C.CmpC -> HoistM PrimOp
hoistCmp (C.EqC x y) = PrimEqInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.NeC x y) = PrimNeInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.LtC x y) = PrimLtInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.LeC x y) = PrimLeInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.GtC x y) = PrimGtInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.GeC x y) = PrimGeInt64 <$> hoistVarOcc x <*> hoistVarOcc y



declareClosureNames :: (a -> C.Name) -> [a] -> HoistM [(ClosureName, a)]
declareClosureNames closureName cs =
  for cs $ \def -> do
    let
      pickName f ds =
        let d = asClosureName f in
        case Set.member d ds of
          False -> (d, Set.insert d ds)
          True -> pickName (C.prime f) ds
    decls <- get
    let (d, decls') = pickName (closureName def) decls
    put decls'
    pure (d, def)


-- | Replace the set of fields and places in the environment, while leaving the
-- set of declaration names intact. This is because inside a closure, all names
-- refer to either a local variable/parameter (a place), a captured variable (a
-- field), or to a closure that has been hoisted to the top level (a decl)
inClosure :: C.EnvDef -> [C.ClosureParam] -> ((Id, EnvDecl) -> [ClosureParam] -> HoistM a) -> HoistM a
inClosure env params k = do
  withEnvDef env $ \env' ->
    withParams params $ \params' ->
      k env' params'

withParams :: [C.ClosureParam] -> ([ClosureParam] -> HoistM a) -> HoistM a
withParams params k = local setScope $ k params'
  where
    setScope (HoistEnv _ oldEnv) = HoistEnv newLocals oldEnv
    newLocals = Scope places' infoPlaces'
    -- Hmm. Technically, this should probably be a foldl, not a foldr.
    -- This is because later entries in the telescope should shadow earlier ones.
    -- I'm just going to ignore that problem, though, and assume that names in
    -- the same telescope are unique.
    -- (Also, I would need to snoc the new H.ClosureParam, which is a pain.)
    (places', infoPlaces', params') = foldr f (Map.empty, Map.empty, []) params
    f (C.TypeParam aa) (places, infoPlaces, tele) =
      let aa' = asInfoPlace aa in
      (places, Map.insert (asTyVar aa) aa' infoPlaces, TypeParam aa' : tele)
    f (C.ValueParam x s) (places, infoPlaces, tele) =
      let p = asPlace s x in
      (Map.insert x p places, infoPlaces, PlaceParam p : tele)

withEnvDef :: C.EnvDef -> ((Id, EnvDecl) -> HoistM a) -> HoistM a
withEnvDef (C.EnvDef tyfields fields) k = do
  let fields' = map (\ (x, s) -> (x, asPlace s x)) fields
  let tyfields' = map (\aa -> (asTyVar aa, asInfoPlace aa)) tyfields
  let newEnv = Scope (Map.fromList fields') (Map.fromList tyfields')
  -- TODO: Convert tyfields' to [InfoPlace2]
  let envd = EnvDecl (map snd tyfields') (map snd fields')
  local (\ (HoistEnv oldLocals _) -> HoistEnv oldLocals newEnv) $ do
    -- Pick the environment pointer's name based on the in-scope set
    -- *after* we are in the closure's context
    envp <- pickEnvironmentName
    k (envp, envd)

-- | Pick a name for the environment parameter, that will not clash with
-- anything already in scope.
pickEnvironmentName :: HoistM Id
pickEnvironmentName = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places infos) = foldMap (Set.singleton . placeName) places <> foldMap (Set.singleton . infoName) infos
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id ("env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))

pickEnvironmentPlace :: Id -> HoistM Id
pickEnvironmentPlace (Id cl) = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places infos) = foldMap (Set.singleton . placeName) places <> foldMap (Set.singleton . infoName) infos
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id (cl ++ "_env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))

hoistClosureAllocs :: (a -> C.Name) -> (a -> C.Sort) -> (a -> C.EnvDef) -> [(ClosureName, a)] -> C.TermC -> HoistM TermH
hoistClosureAllocs closureName closureSort closureEnvDef cdecls e = do
  placesForClosureAllocs closureName closureSort cdecls $ \cplaces -> do
    cs' <- for cplaces $ \ (p, d, def) -> do
      env' <- hoistEnvDef (Set.fromList (map (closureName . snd) cdecls)) (closureEnvDef def)
      envPlace <- pickEnvironmentPlace (placeName p)
      pure (ClosureAlloc p d envPlace env')
    e' <- hoist e
    pure (AllocClosure cs' e')

placesForClosureAllocs :: (a -> C.Name) -> (a -> C.Sort) -> [(ClosureName, a)] -> ([(Place, ClosureName, a)] -> HoistM r) -> HoistM r
placesForClosureAllocs closureName closureSort cdecls kont = do
  scope <- asks (scopePlaces . localScope)
  let
    pickPlace sc (d, def) =
      let (cname, csort) = (closureName def, closureSort def) in
      let c = go sc cname in
      let p = asPlace csort c in
      (Map.insert cname p sc, (p, d, def))
    go sc c = case Map.lookup c sc of
      Nothing -> c
      Just _ -> go sc (C.prime c)
  let (scope', cplaces) = mapAccumL pickPlace scope cdecls
  let extend (HoistEnv (Scope _ fields) env) = HoistEnv (Scope scope' fields) env
  local extend (kont cplaces)

hoistEnvDef :: Set C.Name -> C.EnvDef -> HoistM EnvAlloc
hoistEnvDef recNames (C.EnvDef tys fields) = do
  tyfields <- traverse envAllocInfo tys
  fields' <- traverse (envAllocField recNames) fields
  pure (EnvAlloc tyfields fields')

envAllocInfo :: C.TyVar -> HoistM (InfoPlace, Info)
envAllocInfo aa = do
  let info = asInfoPlace aa
  -- This is sketchy. Figure out how it should really work.
  i <- infoForTyVar (asTyVar aa)
  pure (info, i)

envAllocField :: Set C.Name -> (C.Name, C.Sort) -> HoistM EnvAllocArg
envAllocField recNames (x, s) = case Set.member x recNames of
  False -> EnvFreeArg (asPlace s x) <$> hoistVarOcc x
  True -> EnvRecArg (asPlace s x) <$> hoistVarOcc x



-- | Hoist a variable occurrence, and also retrieve its sort.
hoistVarOccSort :: C.Name -> HoistM (Name, Sort)
hoistVarOccSort x = do
  ps <- asks (scopePlaces . localScope)
  fs <- asks (scopePlaces . envScope)
  case Map.lookup x ps of
    Just (Place s x') -> pure (LocalName x', s)
    Nothing -> case Map.lookup x fs of
      Just (Place s x') -> pure (EnvName x', s)
      Nothing -> error ("not in scope: " ++ show x)

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc = fmap fst . hoistVarOccSort

-- | Hoist a list of arguments.
hoistArgList :: [C.Name] -> HoistM [ClosureArg]
hoistArgList xs = traverse f xs
  where
    f x = hoistVarOccSort x >>= \case
      (x', AllocH aa) -> OpaqueArg x' <$> infoForTyVar aa
      (x', _) -> pure (ValueArg x')

-- | Hoist a variable occurrence, and also retrieve the @type_info@ that describes it.
hoistVarOccInfo :: C.Name -> HoistM (Name, Info)
hoistVarOccInfo x = do
  (x', s) <- hoistVarOccSort x
  s' <- infoForSort s
  pure (x', s')

infoForSort :: Sort -> HoistM Info
infoForSort (AllocH aa) = infoForTyVar aa
infoForSort IntegerH = pure Int64Info
infoForSort BooleanH = pure BoolInfo
infoForSort UnitH = pure UnitInfo
infoForSort SumH = pure SumInfo
infoForSort StringH = pure StringInfo
infoForSort (ProductH _ _) = pure ProductInfo
infoForSort (ListH _) = pure ListInfo
infoForSort (ClosureH _) = pure ClosureInfo

infoForTyVar :: TyVar -> HoistM Info
infoForTyVar aa = do
  iplaces <- asks (scopeInfos . localScope)
  ifields <- asks (scopeInfos . envScope)
  case Map.lookup aa iplaces of
    Just (InfoPlace aa') -> pure (LocalInfo aa')
    Nothing -> case Map.lookup aa ifields of
      Just (InfoPlace aa') -> pure (EnvInfo aa')
      Nothing -> error ("not in scope: " ++ show aa)

-- | Bind a place name of the appropriate sort, running a monadic action in the
-- extended environment.
withPlace :: C.Name -> C.Sort -> HoistM a -> HoistM (Place, a)
withPlace x s m = do
  x' <- makePlace x s
  let f (HoistEnv (Scope places fields) env) = HoistEnv (Scope (Map.insert x x' places) fields) env
  a <- local f m
  pure (x', a)

makePlace :: C.Name -> C.Sort -> HoistM Place
makePlace x s = do
  places <- asks (scopePlaces . localScope)
  go x places
  where
    -- I think this is fine. We might shadow local names, which is bad, but
    -- environment references are guarded by 'env->'.
    go :: C.Name -> Map C.Name Place -> HoistM Place
    go v ps = case Map.lookup v ps of
      Nothing -> pure (asPlace s v)
      Just _ -> go (C.prime v) ps



