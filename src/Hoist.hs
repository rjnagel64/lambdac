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
import Control.Monad.Writer
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

insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

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
sortOf C.Character = CharH
sortOf (C.Pair t s) = ProductH (sortOf t) (sortOf s)
sortOf (C.Record fields) = RecordH (map sortOfField fields)
  where sortOfField (f, t) = (hoistFieldLabel f, sortOf t)
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

caseKind :: C.TyConApp -> TyConApp
caseKind (C.TyConApp (C.TyCon tc) args) = TyConApp (TyCon tc) (map sortOf args)



-- Hmm. Instead of 'Writer', would an 'Update' monad be applicable here?
newtype HoistM a = HoistM { runHoistM :: ReaderT HoistEnv (StateT (Set CodeLabel) (Writer ClosureDecls)) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter ClosureDecls HoistM
deriving newtype instance MonadState (Set CodeLabel) HoistM

data HoistEnv =
  HoistEnv {
    localScope :: Map C.Name Place
  , envScope :: Map C.Name Place
  , nameRefs :: Map C.Name Name
  }

data Scope = Scope (Map C.Name Place)

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
    emptyEnv = HoistEnv { localScope = Map.empty, envScope = Map.empty, nameRefs = Map.empty }


hoistDataDecls :: [C.DataDecl] -> [DataDecl]
hoistDataDecls [] = []
hoistDataDecls (C.DataDecl (C.TyCon tc) params ctors : ds) = DataDecl (TyCon tc) kind ctors' : hoistDataDecls ds
  where
    kind = foldr (\ (_, k1) k2 -> KArr (kindOf k1) k2) Star params
    params' = map (\ (aa, k) -> (asTyVar aa, kindOf k)) params
    ctors' = map (hoistCtorDecl params') ctors

hoistCtorDecl :: [(TyVar, Kind)] -> C.CtorDecl -> CtorDecl
hoistCtorDecl params' (C.CtorDecl (C.Ctor c) args) = CtorDecl (Ctor c) params' (zipWith f [0..] args)
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
hoist (C.IfC x k1 k2) = do
  x' <- hoistVarOcc x
  k1' <- hoistVarOcc k1
  k2' <- hoistVarOcc k2
  pure $ IfH x' k1' k2'
hoist (C.CaseC x t ks) = do
  x' <- hoistVarOcc x
  let kind = caseKind t
  ks' <- traverse (\ (C.Ctor c, k) -> (,) <$> pure (Ctor c) <*> hoistVarOcc k) ks
  pure $ CaseH x' kind ks'
hoist (C.LetValC (x, s) v e) = do
  v' <- hoistValue v
  withPlace x s $ \x' -> do
    e' <- hoist e
    pure (LetValH x' v' e')
hoist (C.LetFstC (x, s) y e) = do
  y' <- hoistVarOcc y
  withPlace x s $ \x' -> do
    e' <- hoist e
    pure (LetProjectH x' y' ProjectFst e')
hoist (C.LetSndC (x, s) y e) = do
  y' <- hoistVarOcc y
  withPlace x s $ \x' -> do
    e' <- hoist e
    pure (LetProjectH x' y' ProjectSnd e')
hoist (C.LetFieldC (x, s) y f e) = do
  y' <- hoistVarOcc y
  let f' = hoistFieldLabel f
  withPlace x s $ \x' -> do
    e' <- hoist e
    pure (LetProjectH x' y' (ProjectField f') e')
hoist (C.LetArithC (x, s) op e) = do
  op' <- hoistArith op
  withPlace x s $ \x' -> do
    e' <- hoist e
    pure (LetPrimH x' op' e')
hoist (C.LetCompareC (x, s) op e) = do
  op' <- hoistCmp op
  withPlace x s $ \x' -> do
    e' <- hoist e
    pure (LetPrimH x' op' e')
hoist (C.LetStringOpC (x, s) op e) = do
  op' <- hoistStringOp op
  withPlace x s $ \x' -> do
    e' <- hoist e
    pure (LetPrimH x' op' e')
hoist (C.LetBindC (x1, s1) (x2, s2) op e) = do
  op' <- hoistPrimIO op
  withPlace x1 s1 $ \x1' -> do
    withPlace x2 s2 $ \x2' -> do
      e' <- hoist e
      pure (LetBindH x1' x2' op' e')
hoist (C.LetFunC fs e) = do
  let
    (fbinds, fs') = unzip $ map (\def@(C.FunClosureDef f _ _ _) -> 
      let p = asPlace (C.funClosureSort def) f in
      ((f, p), (p, def))) fs

  let fbinds' = [(f, LocalName (placeName f')) | (f, f') <- fbinds]
  let extend env = env { localScope = insertMany fbinds (localScope env), nameRefs = insertMany fbinds' (nameRefs env) }
  local extend $ do
    allocs <- for fs' $ \ (p, C.FunClosureDef f env params body) -> do
      -- Pick a name for the closure's code
      fcode <- nameClosureCode f
      envp <- pickEnvironmentPlace (placeName p)

      (envd, Scope newEnv) <- hoistEnvDef env

      -- hoist the closure code and emit
      let (Scope newLocals, params') = convertParameters params
      -- TODO: Extend nameRefs with newLocals
      local (\env -> HoistEnv newLocals newEnv (nameRefs env)) $ do
        envn <- pickEnvironmentName
        body' <- hoist body
        let decl = CodeDecl fcode (envn, envd) params' body'
        tellClosure decl

      enva <- hoistEnvAlloc env
      let alloc = ClosureAlloc p fcode envp enva
      pure alloc
    e' <- hoist e
    pure (AllocClosure allocs e')
hoist (C.LetContC ks e) = do
  -- Continuation closures are necessarily non-recursive, so this case is
  -- simpler than the case for LetFunC.
  (kbinds, allocs) <- fmap unzip $ traverse (\ (k, def) -> hoistContClosure k def) ks
  let kbinds' = [(k, LocalName (placeName k')) | (k, k') <- kbinds]
  let extend env = env { localScope = insertMany kbinds (localScope env), nameRefs = insertMany kbinds' (nameRefs env) }
  e' <- local extend $ hoist e
  pure (AllocClosure allocs e')

-- hoist (C.LetContC ks e) = do
--   withContClosures ks $ \_ -> do
--     let allocs = _
--     e' <- hoist e
--     pure (AllocClosure allocs e')
--
-- withContClosures :: [(C.Name, C.ContClosureDef)] -> (_ -> HoistM a) -> HoistM a
-- withContClosures ks cont = do
--   -- translate each ContClosureDef to a top-level CodeDecl
--   -- make a ClosureAlloc for each entry
--   -- extend the context
--   -- invoke continuation
--   (kbinds, allocs) <- unzip <$> for ks $ \ (k, C.ContClosureDef env params body) -> do
--     -- invent a code label for this closure
--     -- map 'k' (CC variable) to a Hoist variable
--     -- create a ClosureAlloc describing the code label, etc.
--     -- some nonsense involving the EnvDef (maybe withEnvDef be scoping op, but
--     -- hoistEnvAlloc be occurrence?)
--
--   let extend env = _
--   local extend $ cont _
--
-- hoistEnvAlloc :: C.EnvDef -> HoistM EnvAlloc
-- hoistEnvAlloc (C.EnvDef tys xs) = _
--
-- withEnvDef :: C.EnvDef -> (EnvDef -> HoistM a) -> HoistM a
-- withEnvDef (C.EnvDef tys xs) cont =
--   withTyVars tys $ \tys' -> do
--     withEnvPlaces xs $ \xs' -> do
--       cont (EnvDef tys xs')

hoistContClosure :: C.Name -> C.ContClosureDef -> HoistM ((C.Name, Place), ClosureAlloc)
hoistContClosure k def@(C.ContClosureDef env params body) = do
  let kplace = asPlace (C.contClosureSort def) k
  -- Pick a name for the closure's code
  kcode <- nameClosureCode k
  envp <- pickEnvironmentPlace (placeName kplace)

  (envd, Scope newEnv) <- hoistEnvDef env

  -- hoist the closure code and emit
  let (Scope newLocals, params') = convertParameters (C.makeClosureParams [] params)
  -- TODO: Extend nameRefs with newLocals
  local (\env -> HoistEnv newLocals newEnv (nameRefs env)) $ do
    envn <- pickEnvironmentName
    body' <- hoist body
    let decl = CodeDecl kcode (envn, envd) params' body'
    tellClosure decl

  enva <- hoistEnvAlloc env
  let alloc = ClosureAlloc kplace kcode envp enva
  pure ((k, kplace), alloc)

hoistEnvDef :: C.EnvDef -> HoistM (EnvDecl, Scope)
hoistEnvDef (C.EnvDef tyfields fields) = do
  let declTyFields = map (\ (aa, k) -> (asTyVar aa, kindOf k)) tyfields
  let declFields = map (\ (x, s) -> asPlace s x) fields
  let envd = EnvDecl declTyFields declFields

  let scPlaces = Map.fromList $ map (\ (x, s) -> (x, asPlace s x)) fields
  let envsc = Scope scPlaces
  pure (envd, envsc)

hoistEnvAlloc :: C.EnvDef -> HoistM EnvAlloc
hoistEnvAlloc (C.EnvDef tyfields fields) = do
  -- Note: When allocating a recursive environment, we need to have the current
  -- bind group in scope. consider even-odd:
  -- let
  --   even0 : closure(int, closure(bool)) = #even0 { odd0 = odd0 };
  --   odd0 : closure(int, closure(bool)) = #odd0 { even0 = even0 };
  -- in
  -- ...
  -- In order to construct the environments { odd0 = odd0 } and { even0 = even0 },
  -- we need to have 'even0' and 'odd0' in the local scope.
  --
  -- (I think I take care of this in LetFunC? That's where the recursive group
  -- is)
  let tyFields = map (\ (aa, k) -> AllocH (asTyVar aa)) tyfields
  allocFields <- for fields $ \ (x, s) ->
    (,) (placeName (asPlace s x)) <$> hoistVarOcc x
  let enva = EnvAlloc tyFields allocFields
  pure enva

hoistValue :: C.ValueC -> HoistM ValueH
hoistValue (C.IntC i) = pure (IntH (fromIntegral i))
hoistValue (C.BoolC b) = pure (CtorAppH (BoolH b))
hoistValue (C.PairC x y) =
  PairH <$> hoistVarOcc x <*> hoistVarOcc y
hoistValue (C.RecordC fields) =
  RecordValH <$> traverse hoistField fields
  where hoistField (f, x) = (,) <$> pure (hoistFieldLabel f) <*> hoistVarOcc x
hoistValue C.NilC = pure NilH
hoistValue C.WorldTokenC = pure WorldToken
hoistValue (C.StringC s) = pure (StringValH s)
hoistValue (C.CharC c) = pure (CharValH c)
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
hoistCmp (C.EqCharC x y) = PrimEqChar <$> hoistVarOcc x <*> hoistVarOcc y

hoistStringOp :: C.StringOpC -> HoistM PrimOp
hoistStringOp (C.ConcatC x y) = PrimConcatenate <$> hoistVarOcc x <*> hoistVarOcc y
hoistStringOp (C.IndexC x y) = PrimIndexStr <$> hoistVarOcc x <*> hoistVarOcc y
hoistStringOp (C.LengthC x) = PrimStrlen <$> hoistVarOcc x

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

withParameterList :: [C.ClosureParam] -> ([ClosureParam] -> HoistM a) -> HoistM a
withParameterList [] cont = cont []
withParameterList (C.ValueParam x s : params) cont =
  withPlace x s $ \x' ->
    withParameterList params $ \params' ->
      cont (PlaceParam x' : params')
withParameterList (C.TypeParam aa k : params) cont =
  withTyVar aa k $ \aa' k' ->
    withParameterList params $ \params' ->
      cont (TypeParam aa' k' : params')

-- | Pick a name for the environment parameter, that will not clash with
-- anything already in scope.
pickEnvironmentName :: HoistM Id
pickEnvironmentName = do
  locals <- asks localScope
  env <- asks envScope
  let scopeNames places = foldMap (Set.singleton . placeName) places
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id ("env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))

pickEnvironmentPlace :: Id -> HoistM Id
pickEnvironmentPlace (Id cl) = do
  locals <- asks localScope
  env <- asks envScope
  let scopeNames places = foldMap (Set.singleton . placeName) places
  let scope = scopeNames locals <> scopeNames env
  let go i = let envp = Id (cl ++ "_env" ++ show i) in if Set.member envp scope then go (i+1) else envp
  pure (go (0 :: Int))


-- | Hoist a variable occurrence, and also retrieve its sort.
hoistVarOccSort :: C.Name -> HoistM (Name, Sort)
hoistVarOccSort x = do
  ps <- asks localScope
  fs <- asks envScope
  case Map.lookup x ps of
    Just (Place s x') -> pure (LocalName x', s)
    Nothing -> case Map.lookup x fs of
      Just (Place s x') -> pure (EnvName x', s)
      Nothing -> error ("var not in scope: " ++ show x)

hoistFieldLabel :: C.FieldLabel -> FieldLabel
hoistFieldLabel (C.FieldLabel f) = FieldLabel f

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

-- | Extend the local scope with a new place with the given name and sort.
withPlace :: C.Name -> C.Sort -> (Place -> HoistM a) -> HoistM a
withPlace x s cont = do
  inScope <- asks localScope
  let x' = go x inScope
  let extend env = env { localScope = Map.insert x x' (localScope env), nameRefs = Map.insert x (LocalName (placeName x')) (nameRefs env) }
  local extend $ cont x'
  where
    -- I think this is fine. We might shadow local names, which is bad, but
    -- environment references are guarded by 'env->'.
    go :: C.Name -> Map C.Name Place -> Place
    go v ps = case Map.lookup v ps of
      Nothing -> asPlace s v
      Just _ -> go (C.prime v) ps

-- I don't have scoping for tyvars yet, but this is where it would go.
withTyVar :: C.TyVar -> C.Kind -> (TyVar -> Kind -> HoistM a) -> HoistM a
withTyVar aa k cont = cont (asTyVar aa) (kindOf k)

