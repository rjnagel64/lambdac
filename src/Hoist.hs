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

-- TODO: Be principled about CC.TyVar <-> Hoist.TyVar conversions
asTyVar :: C.TyVar -> TyVar
asTyVar (C.TyVar aa) = TyVar (Id aa)

sortOf :: C.Sort -> Sort
sortOf C.Integer = IntegerH
sortOf C.Boolean = BooleanH
sortOf C.Unit = UnitH
sortOf C.Token = TokenH
sortOf C.String = StringH
sortOf (C.Pair t s) = ProductH (sortOf t) (sortOf s)
sortOf (C.Sum t s) = SumH (sortOf t) (sortOf s)
sortOf (C.Closure ss) = ClosureH (ClosureTele (map f ss))
  where
    f (C.ValueTele s) = ValueTele (sortOf s)
    f (C.TypeTele aa k) = TypeTele (asTyVar aa) (kindOf k)
sortOf (C.Alloc aa) = AllocH (asTyVar aa)
sortOf (C.TyConOcc (C.TyCon tc)) = TyConH (TyCon tc)
sortOf (C.TyApp t s) = TyAppH (sortOf t) (sortOf s)

kindOf :: C.Kind -> Kind
kindOf C.Star = Star
kindOf (C.KArr k1 k2) = KArr (kindOf k1) (kindOf k2)

caseKind :: C.CaseKind -> TyConApp
caseKind C.CaseBool = CaseBool
caseKind (C.CaseSum a b) = CaseSum (sortOf a) (sortOf b)
caseKind (C.TyConApp (C.TyCon tc) args) = TyConApp (TyCon tc) (map sortOf args)



-- Hmm. Instead of 'Writer', would an 'Update' monad be applicable here?
newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set CodeLabel) (Writer ClosureDecls)) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter ClosureDecls HoistM
deriving newtype instance MonadState (Set CodeLabel) HoistM

data HoistEnv = HoistEnv { localScope :: Scope, envScope :: Scope }

data Scope = Scope { scopePlaces :: Map C.Name Place }

-- Hmm. Might consider using a DList here. I think there might be a left-nested
-- append happening.
newtype ClosureDecls = ClosureDecls { getClosureDecls :: [CodeDecl] }

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls


tellClosure :: CodeDecl -> HoistM ()
tellClosure cs = tell (ClosureDecls [cs])


hoistProgram :: C.Program -> Program
hoistProgram (C.Program ds srcC) =
  let ds' = hoistDataDecls ds in
  let (srcH, cs) = runHoist (hoist srcC) in
  Program (map DeclData ds' ++ map DeclCode (getClosureDecls cs)) srcH

runHoist :: HoistM a -> (a, ClosureDecls)
runHoist =
  runWriter .
  flip evalStateT Set.empty .
  flip runReaderT emptyEnv .
  runHoistM
  where
    emptyEnv = HoistEnv emptyScope emptyScope
    emptyScope = Scope Map.empty


hoistDataDecls :: [C.DataDecl] -> [DataDecl]
hoistDataDecls [] = []
hoistDataDecls (C.DataDecl (C.TyCon tc) params ctors : ds) = DataDecl (TyCon tc) params' ctors' : hoistDataDecls ds
  where
    params' = map (\ (aa, k) -> (asTyVar aa, kindOf k)) params
    ctors' = map hoistCtorDecl ctors

hoistCtorDecl :: C.CtorDecl -> CtorDecl
hoistCtorDecl (C.CtorDecl (C.Ctor c) args) = CtorDecl (Ctor c) (zipWith f [0..] args)
  where
    f :: Int -> C.Sort -> (Id, Sort)
    f i s = (Id ("arg" ++ show i), sortOf s)



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
  ks' <- traverse (\ (C.Ctor c, k) -> (,) <$> pure (Ctor c) <*> hoistVarOcc k) ks
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
hoist (C.LetCompareC (x, s) op e) = do
  op' <- hoistCmp op
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' op' e')
hoist (C.LetConcatC (x, s) y z e) = do
  op' <- PrimConcatenate <$> hoistVarOcc y <*> hoistVarOcc z
  (x', e') <- withPlace x s $ hoist e
  pure (LetPrimH x' op' e')
hoist (C.LetBindC (x1, s1) (x2, s2) prim e) = do
  prim' <- hoistPrimIO prim
  (x1', (x2', e')) <- withPlace x1 s1 $ withPlace x2 s2 $ hoist e
  pure (LetBindH x1' x2' prim' e')
hoist (C.LetFunC fs e) = do
  let
    (fbinds, fs') = unzip $ map (\def@(C.FunClosureDef f _ _ _) -> 
      let p = asPlace (C.funClosureSort def) f in
      ((f, p), (p, def))) fs

  let
    extend (HoistEnv (Scope places) envsc) =
      let places' = foldr (uncurry Map.insert) places fbinds in
      HoistEnv (Scope places') envsc
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
        let decl = CodeDecl fcode (envn, envd) params' body'
        tellClosure decl

      let alloc = ClosureAlloc p fcode envp enva
      pure alloc
    e' <- hoist e
    pure (AllocClosure allocs e')
hoist (C.LetContC ks e) = do
  (kbinds, allocs) <- fmap unzip $ traverse (\ (k, def) -> hoistContClosure k def) ks
  let
    extend (HoistEnv (Scope places) envsc) =
      let places' = foldr (uncurry Map.insert) places kbinds in
      HoistEnv (Scope places') envsc
  e' <- local extend $ hoist e
  pure (AllocClosure allocs e')

hoistContClosure :: C.Name -> C.ContClosureDef -> HoistM ((C.Name, Place), ClosureAlloc)
hoistContClosure k def@(C.ContClosureDef env params body) = do
  let kplace = asPlace (C.contClosureSort def) k
  -- Pick a name for the closure's code
  kcode <- nameClosureCode k
  envp <- pickEnvironmentPlace (placeName kplace)

  (envd, newEnv, enva) <- hoistEnvDef env

  -- hoist the closure code and emit
  let (newLocals, params') = convertParameters (C.makeClosureParams [] params)
  local (\ (HoistEnv _ _) -> HoistEnv newLocals newEnv) $ do
    envn <- pickEnvironmentName
    body' <- hoist body
    let decl = CodeDecl kcode (envn, envd) params' body'
    tellClosure decl

  let alloc = ClosureAlloc kplace kcode envp enva
  pure ((k, kplace), alloc)

hoistEnvDef :: C.EnvDef -> HoistM (EnvDecl, Scope, EnvAlloc)
hoistEnvDef (C.EnvDef tyfields fields) = do
  let declTyFields = map (\ (aa, k) -> (asTyVar aa, kindOf k)) tyfields
  let declFields = map (\ (x, s) -> asPlace s x) fields
  let envd = EnvDecl declTyFields declFields

  let scPlaces = Map.fromList $ map (\ (x, s) -> (x, asPlace s x)) fields
  let envsc = Scope scPlaces

  -- Note: When allocating a recursive environment, we need to have the current
  -- bind group in scope. consider even-odd:
  -- let
  --   even0 : closure(int, closure(bool)) = #even0 { odd0 = odd0 };
  --   odd0 : closure(int, closure(bool)) = #odd0 { even0 = even0 };
  -- in
  -- ...
  -- In order to construct the environments { odd0 = odd0 } and { even0 = even0 },
  -- we need to have 'even0' and 'odd0' in the local scope.
  let tyFields = map (\ (aa, k) -> AllocH (asTyVar aa)) tyfields
  allocFields <- for fields $ \ (x, s) ->
    (,) (placeName (asPlace s x)) <$> hoistVarOcc x
  let enva = EnvAlloc tyFields allocFields
  pure (envd, envsc, enva)

hoistValue :: C.ValueC -> HoistM ValueH
hoistValue (C.IntC i) = pure (IntH (fromIntegral i))
hoistValue (C.BoolC b) = pure (CtorAppH (BoolH b))
hoistValue (C.PairC x y) =
  PairH <$> hoistVarOcc x <*> hoistVarOcc y
hoistValue C.NilC = pure NilH
hoistValue C.WorldTokenC = pure WorldToken
hoistValue (C.InlC x) = (CtorAppH . InlH) <$> hoistVarOcc x
hoistValue (C.InrC x) = (CtorAppH . InrH) <$> hoistVarOcc x
hoistValue (C.StringC s) = pure (StringValH s)
hoistValue (C.CtorAppC (C.Ctor c) args) = (CtorAppH . CtorApp (Ctor c)) <$> traverse hoistVarOcc args

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

hoistPrimIO :: C.PrimIO -> HoistM PrimIO
hoistPrimIO (C.GetLineC x) = PrimGetLine <$> hoistVarOcc x
hoistPrimIO (C.PutLineC x y) = PrimPutLine <$> hoistVarOcc x <*> hoistVarOcc y


nameClosureCode :: C.Name -> HoistM CodeLabel
nameClosureCode c@(C.Name x i) = do
  let c' = CodeLabel (x ++ show i)
  decls <- get
  if Set.notMember c' decls then
    put (Set.insert c' decls) *> pure c'
  else
    nameClosureCode (C.prime c)

convertParameters :: [C.ClosureParam] -> (Scope, [ClosureParam])
convertParameters params = (Scope places, params')
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
    (places, params') =
      let (ps, te) = foldr addParam (id, []) params in
      (ps Map.empty, te)

    addParam (C.TypeParam aa k) (ps, tele) =
      let aa' = asTyVar aa in
      (ps, TypeParam aa' (kindOf k) : tele)
    addParam (C.ValueParam x s) (ps, tele) =
      let p = asPlace s x in
      (ps . Map.insert x p, PlaceParam p : tele)

-- | Pick a name for the environment parameter, that will not clash with
-- anything already in scope.
pickEnvironmentName :: HoistM Id
pickEnvironmentName = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places) = foldMap (Set.singleton . placeName) places
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id ("env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))

pickEnvironmentPlace :: Id -> HoistM Id
pickEnvironmentPlace (Id cl) = do
  HoistEnv locals env <- ask
  let scopeNames (Scope places) = foldMap (Set.singleton . placeName) places
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
  inScope <- asks (scopePlaces . localScope)
  x' <- go x inScope
  let extend (HoistEnv (Scope places) env) = HoistEnv (Scope (Map.insert x x' places)) env
  a <- local extend m
  pure (x', a)
  where
    -- I think this is fine. We might shadow local names, which is bad, but
    -- environment references are guarded by 'env->'.
    go :: C.Name -> Map C.Name Place -> HoistM Place
    go v ps = case Map.lookup v ps of
      Nothing -> pure (asPlace s v)
      Just _ -> go (C.prime v) ps


