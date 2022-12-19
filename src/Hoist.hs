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

import Data.Traversable (for)

import qualified CC.IR as C

import Hoist.IR hiding (Subst, singleSubst, substSort)


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
asTyVar (C.TyVar aa) = TyVar (Id aa)

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
    f (C.TypeTele aa k) = TypeTele (asTyVar aa)
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

-- Hmm. Might consider using a DList here. I think there might be a left-nested
-- append happening.
newtype ClosureDecls = ClosureDecls { getClosureDecls :: [ClosureDecl] }

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls


tellClosure :: ClosureDecl -> HoistM ()
tellClosure cs = tell (ClosureDecls [cs])


hoistProgram :: C.TermC -> Program
hoistProgram srcC =
  let (srcH, cs) = runHoist (hoist srcC) in
  Program (getClosureDecls cs) srcH

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
  ys <- hoistArgList (map C.ValueArg xs)
  pure (OpenH k' ys)
hoist (C.CallC f xs ks) = do
  f' <- hoistVarOcc f
  ys <- hoistArgList (xs ++ map C.ValueArg ks)
  pure (OpenH f' ys)
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
-- TODO: Hoist for closures is absurdly convoluted. There must be a simpler formulation.
-- The current version does three passes over the list of definitions
hoist (C.LetFunC fs e) = do
  let
    (fbinds, fs') = unzip $ map (\def@(C.FunClosureDef f _ _ _) -> 
      let p = asPlace (C.funClosureSort def) f in
      ((f, p), (p, def))) fs

  let
    extend (HoistEnv (Scope places infos) envsc) =
      let places' = foldr (uncurry Map.insert) places fbinds in
      HoistEnv (Scope places' infos) envsc
  local extend $ do
    allocs <- for fs' $ \ (p, def@(C.FunClosureDef f env params body)) -> do
      -- Pick a name for the closure, based on 'f'
      fcode <- pickClosureName f
      envp <- pickEnvironmentPlace (placeName p)

      (envd, newEnv, enva) <- hoistEnvDef env

      -- hoist the closure code and emit
      let (newLocals, params') = convertParameters params
      local (\ (HoistEnv _ _) -> HoistEnv newLocals newEnv) $ do
        envn <- pickEnvironmentName
        body' <- hoist body
        let decl = ClosureDecl fcode (envn, envd) params' body'
        tellClosure decl

      let alloc = ClosureAlloc p fcode envp enva
      pure alloc
    e' <- hoist e
    pure (AllocClosure allocs e')
hoist (C.LetContC ks e) = do
  let
    (kbinds, ks') = unzip $ map (\def@(C.ContClosureDef k _ _ _) -> 
      let p = asPlace (C.contClosureSort def) k in
      ((k, p), (p, def))) ks

  let
    extend (HoistEnv (Scope places infos) envsc) =
      let places' = foldr (uncurry Map.insert) places kbinds in
      HoistEnv (Scope places' infos) envsc
  local extend $ do
    allocs <- for ks' $ \ (p, def@(C.ContClosureDef k env params body)) -> do
      -- Pick a name for the closure, based on 'k'
      kcode <- pickClosureName k
      envp <- pickEnvironmentPlace (placeName p)

      (envd, newEnv, enva) <- hoistEnvDef env

      -- hoist the closure code and emit
      let (newLocals, params') = convertParameters (C.makeClosureParams [] params)
      local (\ (HoistEnv _ _) -> HoistEnv newLocals newEnv) $ do
        envn <- pickEnvironmentName
        body' <- hoist body
        let decl = ClosureDecl kcode (envn, envd) params' body'
        tellClosure decl

      let alloc = ClosureAlloc p kcode envp enva
      pure alloc
    e' <- hoist e
    pure (AllocClosure allocs e')

hoistEnvDef :: C.EnvDef -> HoistM (EnvDecl, Scope, EnvAlloc)
hoistEnvDef (C.EnvDef tyfields fields) = do
  let declTyFields = map (\ (aa, k) -> (infoName (asInfoPlace aa), asTyVar aa)) tyfields
  let declFields = map (\ (x, s) -> asPlace s x) fields
  let envd = EnvDecl declTyFields declFields

  let scPlaces = Map.fromList $ map (\ (x, s) -> (x, asPlace s x)) fields
  let scInfoPlaces = Map.fromList $ map (\ (aa, k) -> (asTyVar aa, asInfoPlace aa)) tyfields
  let envsc = Scope scPlaces scInfoPlaces

  -- Note: When allocating a recursive environment, we need to have the current
  -- bind group in scope. consider even-odd:
  -- let
  --   even0 : closure(int, closure(bool)) = #even0 { odd0 = odd0 };
  --   odd0 : closure(int, closure(bool)) = #odd0 { even0 = even0 };
  -- in
  -- ...
  -- In order to construct the environments { odd0 = odd0 } and { even0 = even0 },
  -- we need to have 'even0' and 'odd0' in the local scope.
  allocTyFields <- for tyfields $ \ (aa, k) ->
    EnvInfoArg (infoName (asInfoPlace aa)) <$> infoForTyVar (asTyVar aa)
  allocFields <- for fields $ \ (x, s) ->
    EnvValueArg (placeName (asPlace s x)) <$> hoistVarOcc x
  let enva = EnvAlloc allocTyFields allocFields
  pure (envd, envsc, enva)

hoistFunClosure :: (ClosureName, C.FunClosureDef) -> HoistM ()
hoistFunClosure (fdecl, C.FunClosureDef _f env tele body) = do
  inClosure env tele $ \env' params' -> do
    body' <- hoist body
    let decl = ClosureDecl fdecl env' params' body'
    tellClosure decl

hoistContClosure :: (ClosureName, C.ContClosureDef) -> HoistM ()
hoistContClosure (kdecl, C.ContClosureDef _k env xs body) = do
  let tele = C.makeClosureParams [] xs
  inClosure env tele $ \env' params' -> do
    body' <- hoist body
    let decl = ClosureDecl kdecl env' params' body'
    tellClosure decl

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


pickClosureName :: C.Name -> HoistM ClosureName
pickClosureName c = do
  decls <- get
  let asClosureName (C.Name x i) = ClosureName (x ++ show i)
  let c' = asClosureName c
  if Set.notMember c' decls then
    put (Set.insert c' decls) *> pure c'
  else
    pickClosureName (C.prime c)

declareClosureNames :: (a -> C.Name) -> [a] -> HoistM [(ClosureName, a)]
declareClosureNames closureName cs = traverse declareClosure cs
  where declareClosure def = (\d -> (d, def)) <$> pickClosureName (closureName def)

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
    (newLocals, params') = convertParameters params

convertParameters :: [C.ClosureParam] -> (Scope, [ClosureParam])
convertParameters params = (Scope places infoPlaces, params')
  where
    -- The reason why this fold looks weird is because it uses the
    -- foldl-via-foldr trick: using a chain of updates as the accumulating
    -- parameter.
    --
    -- This is because place and info parameters are supposed to be extended
    -- from left to right, but using foldl directly would mean repeated snoc
    -- operations to build the Hoist parameter telescope
    --
    -- I guess I could have used foldl and a DList H.ClosureParam, but eh, whatever.
    (places, infoPlaces, params') =
      let (ps, is, te) = foldr addParam (id, id, []) params in
      (ps Map.empty, is Map.empty, te)

    addParam (C.TypeParam aa k) (ps, is, tele) =
      let aa' = asInfoPlace aa in
      (ps, is . Map.insert (asTyVar aa) aa', TypeParam aa' : tele)
    addParam (C.ValueParam x s) (ps, is, tele) =
      let p = asPlace s x in
      (ps . Map.insert x p, is, PlaceParam p : tele)

withEnvDef :: C.EnvDef -> ((Id, EnvDecl) -> HoistM a) -> HoistM a
withEnvDef (C.EnvDef tyfields fields) k = do
  let fields' = map (\ (x, s) -> (x, asPlace s x)) fields
  let tyfields' = map (\ (aa, k) -> (asTyVar aa, asInfoPlace aa)) tyfields
  let newEnv = Scope (Map.fromList fields') (Map.fromList tyfields')
  let envd = EnvDecl (map (\ (aa, i) -> (infoName i, aa)) tyfields') (map snd fields')
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

hoistClosureAllocs :: ((ClosureName, a) -> HoistM ()) -> (a -> C.Name) -> (a -> C.Sort) -> (a -> C.EnvDef) -> [(ClosureName, a)] -> C.TermC -> HoistM TermH
hoistClosureAllocs hoistClosure closureName closureSort closureEnvDef cdecls e = do
  let
    makeClosurePlace (d, def) = do
      hoistClosure (d, def)
      let cname = closureName def
      let p = asPlace (closureSort def) cname
      pure ((cname, p), (p, d, def))
  (binds, places) <- fmap unzip $ traverse makeClosurePlace cdecls

  local (extend binds) $ do
    cs' <- for places $ \ (p, d, def) -> do
      envAlloc <- hoistEnvAlloc (closureEnvDef def)
      envPlace <- pickEnvironmentPlace (placeName p)
      pure (ClosureAlloc p d envPlace envAlloc)
    e' <- hoist e
    pure (AllocClosure cs' e')
  where
    extend binds (HoistEnv (Scope scope fields) env) =
      let scope' = foldr (uncurry Map.insert) scope binds in
      HoistEnv (Scope scope' fields) env

-- | When constructing a closure, translate a CC-style environment @{ aa+; x+ }@
-- into a Hoist-style environment allocation @{ (aa_info = i)+; (x = v)+ }@.
--
-- I'm not quite satisfied with this function. In particular, I feel like
-- there's a disconnect between how I translate the definition of an
-- environment versus the allocation of that environment.
--
-- (The same work being done 1.5 times, implicitly keeping track of field
-- names, etc.)
--
-- However I fix it, I think if would probably be a good idea if that function
-- returns both a H.EnvDecl and a H.EnvAlloc.
hoistEnvAlloc :: C.EnvDef -> HoistM EnvAlloc
hoistEnvAlloc (C.EnvDef tys fields) = do
  tyfields <- for tys $ \ (aa, k) -> do
    let fieldName = infoName $ asInfoPlace aa
    -- This is *probably* a legit use of 'asTyVar'. CC gives us an environment
    -- consisting of captured free vars, and captured fields.
    -- Now, for each capture tyvar 'aa', we want to construct the value that will
    -- be stored in the closure environment: 'info aa'.
    i <- infoForTyVar (asTyVar aa)
    pure (EnvInfoArg fieldName i)
  fields' <- for fields $ \ (x, s) ->
    let fieldName = placeName (asPlace s x) in
    EnvValueArg fieldName <$> hoistVarOcc x
  pure (EnvAlloc tyfields fields')



-- | Hoist a variable occurrence, and also retrieve its sort.
hoistVarOccSort :: C.Name -> HoistM (Name, Sort)
hoistVarOccSort x = do
  ps <- asks (scopePlaces . localScope)
  fs <- asks (scopePlaces . envScope)
  case Map.lookup x ps of
    Just (Place s x') -> pure (LocalName x', s)
    Nothing -> case Map.lookup x fs of
      Just (Place s x') -> pure (EnvName x', s)
      Nothing -> error ("var not in scope: " ++ show x)

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc = fmap fst . hoistVarOccSort

-- | Hoist a list of arguments.
hoistArgList :: [C.Argument] -> HoistM [ClosureArg]
hoistArgList xs = traverse f xs
  where
    f (C.TypeArg t) = TypeArg <$> infoForSort (sortOf t)
    f (C.ValueArg x) = hoistVarOccSort x >>= \case
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
      Nothing -> error ("tyvar not in scope: " ++ show aa)

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



