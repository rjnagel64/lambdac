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

-- | Given a 'CC.TyVar', compute the 'Id' that references that tyvar's 'Info'
infoPlaceName :: C.TyVar -> Id
infoPlaceName (C.TyVar aa) = Id aa

-- TODO: Be principled about CC.TyVar <-> Hoist.TyVar conversions
asTyVar :: C.TyVar -> TyVar
asTyVar (C.TyVar aa) = TyVar (Id aa)

sortOf :: C.Sort -> Sort
sortOf C.Integer = IntegerH
sortOf C.Boolean = BooleanH
sortOf C.Unit = UnitH
sortOf C.String = StringH
sortOf (C.Pair t s) = ProductH (sortOf t) (sortOf s)
sortOf (C.Sum t s) = SumH (sortOf t) (sortOf s)
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
--
-- 'scopeInfos' maps an in-scope (hoist) type variable to the 'Id' of an info
-- that describes that type.
data Scope = Scope { scopePlaces :: Map C.Name Place, scopeInfos :: Map TyVar Id }

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
  pure (HaltH s x')
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
  let
    (fbinds, fs') = unzip $ map (\def@(C.FunClosureDef f _ _ _) -> 
      let p = asPlace (C.funClosureSort def) f in
      ((f, p), (p, def))) fs

  let
    extend (HoistEnv (Scope places infos) envsc) =
      let places' = foldr (uncurry Map.insert) places fbinds in
      HoistEnv (Scope places' infos) envsc
  local extend $ do
    allocs <- for fs' $ \ (p, C.FunClosureDef f env params body) -> do
      -- Pick a name for the closure's code
      fcode <- nameClosureCode f
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
    allocs <- for ks' $ \ (p, C.ContClosureDef k env params body) -> do
      -- Pick a name for the closure's code
      kcode <- nameClosureCode k
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
  let declTyFields = map (\ (aa, k) -> (infoPlaceName aa, asTyVar aa)) tyfields
  let declFields = map (\ (x, s) -> asPlace s x) fields
  let envd = EnvDecl declTyFields declFields

  let scPlaces = Map.fromList $ map (\ (x, s) -> (x, asPlace s x)) fields
  let scInfoPlaces = Map.fromList $ map (\ (aa, k) -> (asTyVar aa, infoPlaceName aa)) tyfields
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
  allocFields <- for fields $ \ (x, s) ->
    EnvValueArg (placeName (asPlace s x)) <$> hoistVarOcc x
  let enva = EnvAlloc allocFields
  pure (envd, envsc, enva)

hoistValue :: C.ValueC -> HoistM ValueH
hoistValue (C.IntC i) = pure (IntH (fromIntegral i))
hoistValue (C.BoolC b) = pure (BoolH b)
hoistValue (C.PairC x y) =
  PairH <$> hoistVarOcc x <*> hoistVarOcc y
hoistValue C.NilC = pure NilH
hoistValue (C.InlC x) = InlH <$> hoistVarOcc x
hoistValue (C.InrC x) = InrH <$> hoistVarOcc x
hoistValue C.EmptyC = pure ListNilH
hoistValue (C.ConsC x xs) =
  ListConsH <$> hoistVarOcc x <*> hoistVarOcc xs
hoistValue (C.StringC s) = pure (StringValH s)

hoistArith :: C.ArithC -> HoistM PrimOp
hoistArith (C.AddC x y) = PrimAddInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistArith (C.SubC x y) = PrimSubInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistArith (C.MulC x y) = PrimMulInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistArith (C.NegC x) = PrimNegInt64 <$> hoistVarOcc x

hoistCmp :: C.CmpC -> HoistM PrimOp
hoistCmp (C.EqC x y) = PrimEqInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.NeC x y) = PrimNeInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.LtC x y) = PrimLtInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.LeC x y) = PrimLeInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.GtC x y) = PrimGtInt64 <$> hoistVarOcc x <*> hoistVarOcc y
hoistCmp (C.GeC x y) = PrimGeInt64 <$> hoistVarOcc x <*> hoistVarOcc y


nameClosureCode :: C.Name -> HoistM ClosureName
nameClosureCode c = do
  decls <- get
  let asClosureName (C.Name x i) = ClosureName (x ++ show i)
  let c' = asClosureName c
  if Set.notMember c' decls then
    put (Set.insert c' decls) *> pure c'
  else
    nameClosureCode (C.prime c)

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
      let aa' = asTyVar aa in
      let i = infoPlaceName aa in
      (ps, is . Map.insert aa' i, TypeParam aa' : tele)
    addParam (C.ValueParam x s) (ps, is, tele) =
      let p = asPlace s x in
      (ps . Map.insert x p, is, PlaceParam p : tele)

-- | Pick a name for the environment parameter, that will not clash with
-- anything already in scope.
pickEnvironmentName :: HoistM Id
pickEnvironmentName = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places infos) = foldMap (Set.singleton . placeName) places <> foldMap Set.singleton infos
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id ("env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))

pickEnvironmentPlace :: Id -> HoistM Id
pickEnvironmentPlace (Id cl) = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places infos) = foldMap (Set.singleton . placeName) places <> foldMap Set.singleton infos
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id (cl ++ "_env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))


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
    f (C.TypeArg t) = pure (TypeArg (sortOf t))
    f (C.ValueArg x) = hoistVarOccSort x >>= \case
      (x', _) -> pure (ValueArg x')

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



