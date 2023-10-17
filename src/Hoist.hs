
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

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import Data.Bifunctor
import Data.Traversable (for)
import Data.Functor.Compose

import qualified CC.IR as C

import Hoist.IR hiding (Subst, singleSubst, substType)


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

asPlace :: C.Type -> C.Name -> HoistM Place
asPlace s (C.Name x i) = do
  s' <- sortOf s
  u <- freshUnique
  pure (Place s' (Id (x ++ show i) u))

sortOf :: C.Type -> HoistM Type
sortOf C.Integer = pure IntegerH
sortOf C.Boolean = pure BooleanH
sortOf C.Unit = pure UnitH
sortOf C.Token = pure TokenH
sortOf C.String = pure StringH
sortOf C.Character = pure CharH
sortOf (C.Pair t s) = ProductH <$> sortOf t <*> sortOf s
sortOf (C.Record fields) = RecordH <$> traverse sortOfField fields
  where sortOfField (f, t) = (,) (hoistFieldLabel f) <$> sortOf t
sortOf (C.Closure ss) = withClosureTele ss $ \ss' -> pure (ClosureH (ClosureTele ss'))
sortOf (C.Alloc aa) = AllocH <$> hoistTyVarOcc aa
sortOf (C.TyConOcc tc) = TyConH <$> hoistTyConOcc tc
sortOf (C.TyApp t s) = TyAppH <$> sortOf t <*> sortOf s

withClosureTele :: [C.TeleEntry] -> ([TeleEntry] -> HoistM a) -> HoistM a
withClosureTele [] cont = cont []
withClosureTele (C.ValueTele s : ss) cont = do
  s' <- sortOf s
  withClosureTele ss $ \ss' ->
    cont (ValueTele s' : ss')
withClosureTele (C.TypeTele aa k : ss) cont = do
  withTyVar aa k $ \aa' k' ->
    withClosureTele ss $ \ss' ->
      cont (TypeTele aa' k' : ss')

kindOf :: C.Kind -> HoistM Kind
kindOf C.Star = pure Star
kindOf (C.KArr k1 k2) = KArr <$> kindOf k1 <*> kindOf k2

caseKind :: C.TyConApp -> HoistM TyConApp
caseKind (C.TyConApp tc args) = TyConApp <$> hoistTyConOcc tc <*> traverse sortOf args



-- Hmm. Instead of 'Writer', would an 'Update' monad be applicable here?
newtype HoistM a = HoistM { getHoistM :: ReaderT HoistEnv (StateT Unique (Writer ClosureDecls)) a }

deriving newtype instance Functor HoistM
deriving newtype instance Applicative HoistM
deriving newtype instance Monad HoistM
deriving newtype instance MonadReader HoistEnv HoistM
deriving newtype instance MonadWriter ClosureDecls HoistM
deriving newtype instance MonadState Unique HoistM

data HoistEnv =
  HoistEnv {
    nameRefs :: Map C.Name Name
  , nameTypes :: Map C.Name Type
  , tyVarRefs :: Map C.TyVar TyVar
  , ctorTyCons :: Map C.Ctor TyCon
  }

emptyEnv :: HoistEnv
emptyEnv =
  HoistEnv {
    nameRefs = Map.empty
  , nameTypes = Map.empty
  , tyVarRefs = Map.empty
  , ctorTyCons = Map.empty
  }

-- Hmm. Might consider using a DList here. I think there might be a left-nested
-- append happening.
newtype ClosureDecls = ClosureDecls { getClosureDecls :: [CodeDecl] }

deriving newtype instance Semigroup ClosureDecls
deriving newtype instance Monoid ClosureDecls


tellClosure :: CodeDecl -> HoistM ()
tellClosure cs = tell (ClosureDecls [cs])


hoistProgram :: C.Program -> Program
hoistProgram (C.Program ds e) =
  let
    ((dataDecls, mainExpr), cs) = runHoist $ do
      withDataDecls ds $ \ds' -> do
        e' <- hoist e
        pure (ds', e')
  in
    Program (map DeclData dataDecls ++ map DeclCode (getClosureDecls cs)) mainExpr

runHoist :: HoistM a -> (a, ClosureDecls)
runHoist m =
  runWriter $
  flip evalStateT (Unique 0) $
  flip runReaderT emptyEnv $
  getHoistM m

withDataDecls :: [C.DataDecl] -> ([DataDecl] -> HoistM a) -> HoistM a
withDataDecls [] cont = cont []
withDataDecls (C.DataDecl (C.TyCon tc) kind ctors : ds) cont = do
  kind' <- kindOf kind
  let tc' = TyCon tc
  withCtorDecls tc' ctors $ \ctors' ->
    let d' = DataDecl tc' kind' ctors' in
    withDataDecls ds $ \ds' ->
      cont (d' : ds')

withCtorDecls :: TyCon -> [C.CtorDecl] -> ([CtorDecl] -> HoistM a) -> HoistM a
withCtorDecls tc ctors cont = do
  (binds, ctors') <- fmap unzip $ traverse (hoistCtorDecl tc) ctors
  let extend env = env { ctorTyCons = insertMany binds (ctorTyCons env) }
  local extend $ cont ctors'

hoistCtorDecl :: TyCon -> C.CtorDecl -> HoistM ((C.Ctor, TyCon), CtorDecl)
hoistCtorDecl tc (C.CtorDecl (C.Ctor c) params args) =
  withTyVars params $ \params' -> do
    args' <- traverse makeField (zip [0..] args)
    let decl = CtorDecl (Ctor c) params' args'
    pure ((C.Ctor c, tc), decl)
  where
    makeField :: (Int, C.Type) -> HoistM (Id, Type)
    makeField (i, s) = do
      s' <- sortOf s
      u <- freshUnique
      pure (Id ("arg" ++ show i) u, s')



-- | After closure conversion, the code for each function and continuation can
-- be lifted to the top level. Additionally, map value, continuation, and
-- function names to C names.
hoist :: C.TermC -> HoistM TermH
hoist (C.HaltC x) = do
  x' <- hoistVarOcc x
  s <- lookupType x
  pure (HaltH s x')
hoist (C.JumpC k xs) = do
  k' <- hoistVarOcc k
  xs' <- hoistArgList (map C.ValueArg xs)
  pure (OpenH k' xs')
hoist (C.CallC f xs ks) = do
  f' <- hoistVarOcc f
  xs' <- hoistArgList xs
  (allocs, ks') <- hoistCoArgList ks
  if null allocs then
    pure (OpenH f' (xs' ++ map ValueArg ks'))
  else
    pure (AllocClosure allocs (OpenH f' (xs' ++ map ValueArg ks')))
hoist (C.IfC x k1 k2) = do
  x' <- hoistVarOcc x
  (allocs, ks') <- hoistCoArgList [C.ContCoArg k1, C.ContCoArg k2]
  let [k1', k2'] = ks'
  if null allocs then
    pure $ IfH x' k1' k2'
  else
    pure $ AllocClosure allocs (IfH x' k1' k2')
hoist (C.CaseC x t ks) = do
  x' <- hoistVarOcc x
  kind <- caseKind t
  (allocs, ks0') <- hoistCoArgList (Compose ks)
  let ks' = [(Ctor c, k) | (C.Ctor c, k) <- getCompose ks0']
  if null allocs then
    pure $ CaseH x' kind ks'
  else
    pure $ AllocClosure allocs (CaseH x' kind ks')
hoist (C.LetValC (x, t) v e) = do
  hoistValue (toCValue v) $ KNamed x t $ \addBinds -> do
    e' <- hoist e
    pure (addBinds e')
-- hoist (C.LetValC (x, s) v e) = do
--   v' <- hoistValue v
--   withPlace x s $ \x' -> do
--     e' <- hoist e
--     pure (LetValH x' v' e')
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
  withFunClosures fs $ \allocs -> do
    e' <- hoist e
    pure (AllocClosure allocs e')
hoist (C.LetContC ks e) = do
  withContClosures ks $ \allocs -> do
    e' <- hoist e
    pure (AllocClosure allocs e')

withFunClosures :: [C.FunClosureDef] -> ([ClosureAlloc] -> HoistM a) -> HoistM a
withFunClosures fs cont = do
  (fbinds, fs') <- fmap unzip $ for fs $ \def@(C.FunClosureDef f _ _ _) -> do
    p <- asPlace (C.funClosureType def) f
    pure ((f, p), (p, def))

  let fnames = [(f, LocalName (placeName f')) | (f, f') <- fbinds]
  let fsorts = [(f, placeType f') | (f, f') <- fbinds]
  let extend env = env { nameRefs = insertMany fnames (nameRefs env), nameTypes = insertMany fsorts (nameTypes env) }
  local extend $ do
    allocs <- traverse (\ (p, def) -> hoistFunClosure p def) fs'
    cont allocs

withContClosures :: [(C.Name, C.ContClosureDef)] -> ([ClosureAlloc] -> HoistM a) -> HoistM a
withContClosures ks cont = do
  -- Continuation closures are necessarily non-recursive, so this case is
  -- simpler than the case for LetFunC.
  (kbinds, allocs) <- fmap unzip $ traverse (\ (k, def) -> hoistContClosure k def) ks
  let knames = [(k, LocalName (placeName k')) | (k, k') <- kbinds]
  let ksorts = [(k, placeType k') | (k, k') <- kbinds]
  let extend env = env { nameRefs = insertMany knames (nameRefs env), nameTypes = insertMany ksorts (nameTypes env) }
  local extend $ cont allocs

hoistFunClosure :: Place -> C.FunClosureDef -> HoistM ClosureAlloc
hoistFunClosure p (C.FunClosureDef f env params body) = do
  -- Pick a name for the closure's code
  fcode <- nameClosureCode f
  -- Because closure environments are local to this bind group, and shadowing
  -- is permissible in Hoist, just use numeric suffixes for the environment
  -- names.
  u <- freshUnique
  envp <- pure (Id "env" u)

  -- Extend context with environment
  withEnvDef env $ \envd -> do
    -- Extend context with parameter list
    withParameterList params $ \params' -> do
      -- hoist the closure body and emit a code declaration
      withEnvironmentName $ \envn -> do
        body' <- hoist body
        let decl = CodeDecl fcode (envn, envd) params' body'
        tellClosure decl

  enva <- hoistEnvAlloc env
  let alloc = ClosureAlloc p fcode envp enva
  pure alloc

hoistContClosure :: C.Name -> C.ContClosureDef -> HoistM ((C.Name, Place), ClosureAlloc)
hoistContClosure k def@(C.ContClosureDef env params body) = do
  kplace <- asPlace (C.contClosureType def) k
  -- Pick a name for the closure's code
  kcode <- nameClosureCode k
  u <- freshUnique
  envp <- pure (Id "env" u)

  -- Extend context with environment
  withEnvDef env $ \envd -> do
    -- Extend context with parameter list
    withParameterList (C.makeClosureParams [] params) $ \params' -> do
      -- hoist the closure body and emit a code declaration
      withEnvironmentName $ \envn -> do
        body' <- hoist body
        let decl = CodeDecl kcode (envn, envd) params' body'
        tellClosure decl

  enva <- hoistEnvAlloc env
  let alloc = ClosureAlloc kplace kcode envp enva
  pure ((k, kplace), alloc)

withEnvDef :: C.EnvDef -> (EnvDecl -> HoistM a) -> HoistM a
withEnvDef (C.EnvDef tys xs) cont =
  withTyVars tys $ \tys' -> do
    withEnvFields xs $ \xs' -> do
      cont (EnvDecl tys' xs')

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
  tyFields <- traverse (\ (aa, k) -> AllocH <$> hoistTyVarOcc aa) tyfields
  allocFields <- for fields $ \ (x, s) -> do
    -- p <- asPlace s x -- TODO: Convert to field name.
    let f = hoistFieldName x
    x' <- hoistVarOcc x
    pure (f, x')
  let enva = EnvAlloc tyFields allocFields
  pure enva

-- hoistValue :: C.ValueC -> HoistM ValueH
-- hoistValue (C.IntC i) = pure (IntH (fromIntegral i))
-- hoistValue (C.BoolC b) = pure (BoolH b)
-- hoistValue (C.PairC x y) =
--   PairH <$> hoistVarOcc x <*> hoistVarOcc y
-- hoistValue (C.RecordC fields) =
--   RecordValH <$> traverse hoistField fields
--   where hoistField (f, x) = (,) <$> pure (hoistFieldLabel f) <*> hoistVarOcc x
-- hoistValue C.NilC = pure NilH
-- hoistValue C.WorldTokenC = pure WorldToken
-- hoistValue (C.StringC s) = pure (StringValH s)
-- hoistValue (C.CharC c) = pure (CharValH c)
-- hoistValue (C.CtorAppC (C.Ctor c) tyargs args) =
--   CtorAppH (Ctor c) <$> traverse sortOf tyargs <*> traverse hoistVarOcc args

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


freshUnique :: HoistM Unique
freshUnique = do
  u <- get
  modify' (\ (Unique i) -> Unique (i+1))
  pure u

nameClosureCode :: C.Name -> HoistM CodeLabel
nameClosureCode (C.Name x i) = do
  u <- freshUnique
  pure (CodeLabel (x ++ show i) u)

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

withEnvironmentName :: (Id -> HoistM a) -> HoistM a
withEnvironmentName cont = do
  -- In Hoist, there are never actually any references to the environment
  -- pointer, because 'EnvName' uses the envptr implicitly.
  -- Thus, it does not matter if the environment name is shadowed.
  u <- freshUnique
  cont (Id "env" u)


hoistFieldLabel :: C.FieldLabel -> FieldLabel
hoistFieldLabel (C.FieldLabel f) = FieldLabel f

hoistFieldName :: C.Name -> FieldLabel
hoistFieldName (C.Name x i) = FieldLabel (x ++ show i)

-- | Translate a variable reference into either a local reference or an
-- environment reference.
hoistVarOcc :: C.Name -> HoistM Name
hoistVarOcc x = do
  env <- asks nameRefs
  case Map.lookup x env of
    Nothing -> error ("var not in scope: " ++ show x)
    Just x' -> pure x'

hoistTyConOcc :: C.TyCon -> HoistM TyCon
hoistTyConOcc (C.TyCon tc) = pure (TyCon tc)

hoistTyVarOcc :: C.TyVar -> HoistM TyVar
hoistTyVarOcc aa = do
  env <- asks tyVarRefs
  case Map.lookup aa env of
    Nothing -> error ("tyvar not in scope: " ++ show aa)
    Just aa' -> pure aa'

lookupType :: C.Name -> HoistM Type
lookupType x = do
  env <- asks nameTypes
  case Map.lookup x env of
    Nothing -> error ("var not in scope: " ++ show x)
    Just s -> pure s

lookupTyCon :: C.Ctor -> HoistM TyCon
lookupTyCon c = do
  env <- asks ctorTyCons
  case Map.lookup c env of
    Nothing -> error ("ctor not in scope: " ++ show c)
    Just tc -> pure tc

-- | Hoist a list of arguments.
hoistArgList :: [C.Argument] -> HoistM [ClosureArg]
hoistArgList xs = traverse f xs
  where
    f (C.TypeArg t) = TypeArg <$> sortOf t
    f (C.ValueArg x) = ValueArg <$> hoistVarOcc x

hoistCoArgList :: Traversable t => t C.CoArgument -> HoistM ([ClosureAlloc], t Name)
hoistCoArgList ks = do
  (args, (_, allocs)) <- mapAccumLM f ks (0, [])
  pure (allocs, args)
  where
    f (C.VarCoArg k) acc = do
      k' <- hoistVarOcc k
      pure (k', acc)
    f (C.ContCoArg def) (i, allocs) = do
      let k = C.Name "__anon_cont" i
      ((_k, kplace), alloc) <- hoistContClosure k def
      let k' = LocalName (placeName kplace)
      pure (k', (i+1, alloc : allocs))

mapAccumLM :: (Monad m, Traversable t) => (a -> s -> m (b, s)) -> t a -> s -> m (t b, s)
mapAccumLM f xs s = flip runStateT s $ traverse (StateT . f) xs

-- | Extend the local scope with a new place with the given name and sort.
withPlace :: C.Name -> C.Type -> (Place -> HoistM a) -> HoistM a
withPlace x s cont = do
  x' <- asPlace s x
  let xname = LocalName (placeName x')
  let xsort = placeType x'
  let
    extend env =
      env {
        nameRefs = Map.insert x xname (nameRefs env)
      , nameTypes = Map.insert x xsort (nameTypes env)
      }
  local extend $ cont x'

-- I don't have scoping for tyvars yet, but this is where it would go.
withTyVar :: C.TyVar -> C.Kind -> (TyVar -> Kind -> HoistM a) -> HoistM a
withTyVar aa@(C.TyVar x i) k cont = do
  k' <- kindOf k
  let aa' = TyVar x i
  let extend env = env { tyVarRefs = Map.insert aa aa' (tyVarRefs env) }
  local extend $ cont aa' k'


withTyVars :: [(C.TyVar, C.Kind)] -> ([(TyVar, Kind)] -> HoistM a) -> HoistM a
withTyVars [] cont = cont []
withTyVars ((aa, k) : aas) cont =
  withTyVar aa k $ \aa' k' ->
    withTyVars aas $ \aas' ->
      cont ((aa', k') : aas')

withEnvFields :: [(C.Name, C.Type)] -> ([(FieldLabel, Type)] -> HoistM a) -> HoistM a
withEnvFields fields cont = do
  binds <- for fields $ \ (x, s) -> (,) x <$> asPlace s x
  let fields' = [(hoistFieldName x, placeType x') | (x, x') <- binds]
  let newEnvRefs = [(x, EnvName (hoistFieldName x)) | (x, _x') <- binds]
  let newEnvType = [(x, placeType x') | (x, x') <- binds]

  let extend env = env { nameRefs = insertMany newEnvRefs (nameRefs env), nameTypes = insertMany newEnvType (nameTypes env) }
  local extend $ cont fields'

data CValue
  = CVVar C.Name
  | CVPair CValue CValue
  | CVRecord [(C.FieldLabel, CValue)]
  | CVCtor C.Ctor [C.Type] [CValue]
  | CVInt Int
  | CVBool Bool
  | CVString String
  | CVChar Char
  | CVNil
  | CVWorldToken

toCValue :: C.ValueC -> CValue
toCValue (C.PairC x y) = CVPair (CVVar x) (CVVar y)
toCValue (C.RecordC fs) = CVRecord (map (second CVVar) fs)
toCValue (C.IntC i) = CVInt i
toCValue C.NilC = CVNil
toCValue C.WorldTokenC = CVWorldToken
toCValue (C.BoolC b) = CVBool b
toCValue (C.StringC s) = CVString s
toCValue (C.CharC c) = CVChar c
toCValue (C.CtorAppC c ts xs) = CVCtor c ts (map CVVar xs)

-- A continuation, used for flattening values to ANF.
data ANFKont a
  -- Named continuations are used at the top level of a let-bound value
  = KNamed C.Name C.Type ((TermH -> TermH) -> HoistM a)
  -- Anonymous continuations generate names for sub-values
  | KAnon (Name -> Type -> (TermH -> TermH) -> HoistM a)

applyKont :: ANFKont r -> Either Name ValueH -> Type -> (TermH -> TermH) -> HoistM r
applyKont (KNamed x t kont) (Left y') _t' addBinds = do
  t' <- sortOf t
  let extend env = env { nameRefs = Map.insert x y' (nameRefs env), nameTypes = Map.insert x t' (nameTypes env) }
  local extend $ kont (\e' -> addBinds e')
applyKont (KNamed x t kont) (Right v) _t' addBinds =
  withPlace x t $ \x' ->
    kont (\e' -> addBinds (LetValH x' v e'))
applyKont (KAnon kont) (Left y') t' addBinds = do
  kont y' t' (\e' -> addBinds e')
applyKont (KAnon kont) (Right v) t' addBinds = do
  z <- freshTmp
  kont (LocalName z) t' (\e' -> addBinds (LetValH (Place t' z) v e'))

hoistValue :: CValue -> ANFKont a -> HoistM a
hoistValue (CVVar y) kont = do
  y' <- hoistVarOcc y
  t' <- lookupType y
  applyKont kont (Left y') t' (\e' -> e')
hoistValue (CVInt i) kont =
  applyKont kont (Right (IntH (fromIntegral i))) IntegerH (\e' -> e')
hoistValue (CVBool b) kont =
  applyKont kont (Right (BoolH b)) BooleanH (\e' -> e')
hoistValue (CVString s) kont =
  applyKont kont (Right (StringValH s)) StringH (\e' -> e')
hoistValue (CVChar c) kont =
  applyKont kont (Right (CharValH c)) CharH (\e' -> e')
hoistValue CVNil kont =
  applyKont kont (Right NilH) UnitH (\e' -> e')
hoistValue CVWorldToken kont =
  applyKont kont (Right WorldToken) TokenH (\e' -> e')
hoistValue (CVPair v1 v2) kont =
  hoistValue v1 $ KAnon $ \x1 t1 addX1 ->
    hoistValue v2 $ KAnon $ \x2 t2 addX2 ->
      applyKont kont (Right (PairH x1 x2)) (ProductH t1 t2) (addX1 . addX2)
hoistValue (CVRecord fs) kont =
  hoistRecordVal'' fs $ \gs ts addFields ->
    applyKont kont (Right (RecordValH gs)) (RecordH ts) addFields
hoistValue (CVCtor c@(C.Ctor c') ts vs) kont = do
  ts' <- traverse sortOf ts
  tc <- lookupTyCon c
  hoistCtorArgs'' vs $ \vs' addBinds -> do
    let ty = fromTyConApp (TyConApp tc ts')
    applyKont kont (Right (CtorAppH (Ctor c') ts' vs')) ty addBinds

hoistRecordVal'' :: [(C.FieldLabel, CValue)] -> ([(FieldLabel, Name)] -> [(FieldLabel, Type)] -> (TermH -> TermH) -> HoistM a) -> HoistM a
hoistRecordVal'' [] kont = kont [] [] (\e' -> e')
hoistRecordVal'' ((l, v) : ls) kont =
  hoistValue v $ KAnon $ \x t addX ->
    hoistRecordVal'' ls $ \ls' ts addFields -> do
      let l' = hoistFieldLabel l
      kont ((l', x) : ls') ((l', t) : ts) (\e' -> addX (addFields e'))

hoistCtorArgs'' :: [CValue] -> ([Name] -> (TermH -> TermH) -> HoistM a) -> HoistM a
hoistCtorArgs'' [] kont = kont [] (\e' -> e')
hoistCtorArgs'' (v : vs) kont =
  hoistValue v $ KAnon $ \x _t addX ->
    hoistCtorArgs'' vs $ \xs addXs ->
      kont (x : xs) (\e' -> addX (addXs e'))

freshTmp :: HoistM Id
freshTmp = do
  u <- freshUnique
  pure (Id "tmp" u)
