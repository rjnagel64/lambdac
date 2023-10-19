
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
hoist (C.HaltC v) = do
  (x, t, addBinds) <- hoistValue v
  pure (addBinds (HaltH t x))
hoist (C.JumpC k xs) = do
  k' <- hoistVarOcc k
  (addBinds, xs') <- hoistArgList (map C.ValueArg xs)
  pure (addBinds (OpenH k' xs'))
hoist (C.CallC f xs ks) = do
  f' <- hoistVarOcc f
  (addBinds, xs') <- hoistArgList xs
  (addCoBinds, ks') <- hoistCoArgList ks
  pure (addBinds (addCoBinds (OpenH f' (xs' ++ map ValueArg ks'))))
hoist (C.IfC x k1 k2) = do
  x' <- hoistVarOcc x
  (addCoBinds, ks') <- hoistCoArgList [C.ContCoArg k1, C.ContCoArg k2]
  let [k1', k2'] = ks'
  pure (addCoBinds (IfH x' k1' k2'))
hoist (C.CaseC x t ks) = do
  x' <- hoistVarOcc x
  kind <- caseKind t
  (addCoBinds, ks0') <- hoistCoArgList (Compose ks)
  let ks' = [(Ctor c, k) | (C.Ctor c, k) <- getCompose ks0']
  pure (addCoBinds (CaseH x' kind ks'))
hoist (C.LetValC (x, t) v e) = do
  withNamedValue x t v $ \addBinds -> do
    e' <- hoist e
    pure (addBinds e')
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
  fcode <- nameClosureCode p

  -- Extend context with environment
  withEnvDef env $ \envd -> do
    -- Extend context with parameter list
    withParameterList params $ \params' -> do
      -- hoist the closure body and emit a code declaration
      envn <- freshId "env"
      body' <- hoist body
      let decl = CodeDecl fcode (envn, envd) params' body'
      tellClosure decl

  envp <- freshId "env"
  enva <- hoistEnvAlloc env
  let alloc = ClosureAlloc p fcode envp enva
  pure alloc

hoistContClosure :: C.Name -> C.ContClosureDef -> HoistM ((C.Name, Place), ClosureAlloc)
hoistContClosure k def = do
  kplace <- asPlace (C.contClosureType def) k
  alloc <- hoistContClosure' kplace def
  pure ((k, kplace), alloc)

hoistContClosure' :: Place -> C.ContClosureDef -> HoistM ClosureAlloc
hoistContClosure' p (C.ContClosureDef env params body) = do
  kcode <- nameClosureCode p

  withEnvDef env $ \envd -> do
    withParameterList (C.makeClosureParams [] params) $ \params' -> do
      envn <- freshId "env"
      body' <- hoist body
      let decl = CodeDecl kcode (envn, envd) params' body'
      tellClosure decl

  envp <- freshId "env"
  enva <- hoistEnvAlloc env
  let alloc = ClosureAlloc p kcode envp enva
  pure alloc

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
    let f = hoistFieldName x
    x' <- hoistVarOcc x
    pure (f, x')
  let enva = EnvAlloc tyFields allocFields
  pure enva

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

nameClosureCode :: Place -> HoistM CodeLabel
nameClosureCode (Place _s (Id x _u)) = do
  u' <- freshUnique
  pure (CodeLabel x u')

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

addCoBinds :: [ClosureAlloc] -> TermH -> TermH
addCoBinds [] e = e
addCoBinds allocs e = AllocClosure allocs e

hoistArgList :: Traversable t => t C.Argument -> HoistM (TermH -> TermH, t ClosureArg)
hoistArgList xs = do
  (args, binds) <- mapAccumLM f xs (\e' -> e')
  pure (binds, args)
  where
    f (C.TypeArg t) acc = do
      t' <- sortOf t
      pure (TypeArg t', acc)
    f (C.ValueArg v) acc = do
      (x, _t, addBinds) <- hoistValue v
      pure (ValueArg x, acc . addBinds)

hoistCoArgList :: Traversable t => t C.CoArgument -> HoistM (TermH -> TermH, t Name)
hoistCoArgList ks = do
  (args, allocs) <- mapAccumLM f ks []
  if null allocs then
    pure (\e' -> e', args)
  else
    pure (\e' -> AllocClosure allocs e', args)
  where
    -- Annoyingly, it does have to be mapAccumL here. I can't just use
    -- traverse, because turning 't (Maybe ClosureAlloc)' into 't ClosureAlloc'
    -- is Filterable from the 'witherable' package, and I don't feel like
    -- adding a dependency.
    f (C.VarCoArg k) acc = do
      k' <- hoistVarOcc k
      pure (k', acc)
    f (C.ContCoArg def) allocs = do
      kplace <- Place <$> sortOf (C.contClosureType def) <*> freshId "__anon_cont"
      alloc <- hoistContClosure' kplace def
      let k' = LocalName (placeName kplace)
      pure (k', alloc : allocs)

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

-- It's a bit annoying that I have to duplicate logic across these two
-- functions, but the complexity to unify them is worse than the duplication.
withNamedValue :: C.Name -> C.Type -> C.ValueC -> ((TermH -> TermH) -> HoistM a) -> HoistM a
withNamedValue x t (C.VarValC y) kont = do
  y' <- hoistVarOcc y
  t' <- sortOf t
  let extend env = env { nameRefs = Map.insert x y' (nameRefs env), nameTypes = Map.insert x t' (nameTypes env) }
  local extend $ kont (\e' -> e')
withNamedValue x t (C.IntValC i) kont = do
  withPlace x t $ \x' ->
    kont (\e' -> LetValH x' (IntValH (fromIntegral i)) e')
withNamedValue x t (C.BoolValC b) kont = do
  withPlace x t $ \x' ->
    kont (\e' -> LetValH x' (BoolValH b) e')
withNamedValue x t (C.StringValC s) kont = do
  withPlace x t $ \x' ->
    kont (\e' -> LetValH x' (StringValH s) e')
withNamedValue x t (C.CharValC c) kont = do
  withPlace x t $ \x' ->
    kont (\e' -> LetValH x' (CharValH c) e')
withNamedValue x t C.NilValC kont = do
  withPlace x t $ \x' ->
    kont (\e' -> LetValH x' NilValH e')
withNamedValue x t C.TokenValC kont = do
  withPlace x t $ \x' ->
    kont (\e' -> LetValH x' TokenValH e')
withNamedValue x t (C.PairValC v1 v2) kont = do
  (y1, _t1, addY1) <- hoistValue v1
  (y2, _t2, addY2) <- hoistValue v2
  withPlace x t $ \x' ->
    kont (addManyBinds [addY1, addY2] x' (PairValH y1 y2))
withNamedValue x t (C.RecordValC fs) kont = do
  (ys, addYs) <- fmap unzip $ for fs $ \ (f, v) -> do
    let f' = hoistFieldLabel f
    (y, _t, addY) <- hoistValue v
    pure ((f', y), addY)
  withPlace x t $ \x' ->
    kont (addManyBinds addYs x' (RecordValH ys))
withNamedValue x t (C.CtorValC (C.Ctor c) ts vs) kont = do
  ts' <- traverse sortOf ts
  (ys, _ts, addYs) <- fmap unzip3 $ traverse hoistValue vs
  withPlace x t $ \x' ->
    kont (addManyBinds addYs x' (CtorValH (Ctor c) ts' ys))

hoistValue :: C.ValueC -> HoistM (Name, Type, TermH -> TermH)
hoistValue (C.VarValC y) = do
  y' <- hoistVarOcc y
  t <- lookupType y
  pure (y', t, \e' -> e')
hoistValue C.NilValC = do
  tmp <- freshId "tmp"
  let ty = UnitH
  pure (LocalName tmp, ty, \e' -> LetValH (Place ty tmp) NilValH e')
hoistValue C.TokenValC = do
  tmp <- freshId "tmp"
  let ty = TokenH
  pure (LocalName tmp, ty, \e' -> LetValH (Place ty tmp) TokenValH e')
hoistValue (C.IntValC i) = do
  tmp <- freshId "tmp"
  let ty = IntegerH
  pure (LocalName tmp, ty, \e' -> LetValH (Place ty tmp) (IntValH (fromIntegral i)) e')
hoistValue (C.BoolValC b) = do
  tmp <- freshId "tmp"
  let ty = BooleanH
  pure (LocalName tmp, ty, \e' -> LetValH (Place ty tmp) (BoolValH b) e')
hoistValue (C.StringValC s) = do
  tmp <- freshId "tmp"
  let ty = StringH
  pure (LocalName tmp, ty, \e' -> LetValH (Place ty tmp) (StringValH s) e')
hoistValue (C.CharValC c) = do
  tmp <- freshId "tmp"
  let ty = CharH
  pure (LocalName tmp, ty, \e' -> LetValH (Place ty tmp) (CharValH c) e')
hoistValue (C.PairValC v1 v2) = do
  (x, t1, addX) <- hoistValue v1
  (y, t2, addY) <- hoistValue v2
  tmp <- freshId "tmp"
  let ty = ProductH t1 t2
  pure (LocalName tmp, ty, addManyBinds [addX, addY] (Place ty tmp) (PairValH x y))
hoistValue (C.RecordValC fs) = do
  (fs', ts, addFields) <- fmap unzip3 $ for fs $ \ (f, v) -> do
    (x, t, addX) <- hoistValue v
    let f' = hoistFieldLabel f
    pure ((f', x), (f', t), addX)
  tmp <- freshId "tmp"
  let ty = RecordH ts
  pure (LocalName tmp, ty, addManyBinds addFields (Place ty tmp) (RecordValH fs'))
hoistValue (C.CtorValC c@(C.Ctor c') ts vs) = do
  tc <- lookupTyCon c
  ts' <- traverse sortOf ts
  (xs, _ss, addXs) <- fmap unzip3 $ traverse hoistValue vs
  let ty = fromTyConApp (TyConApp tc ts')
  tmp <- freshId "tmp"
  pure (LocalName tmp, ty, addManyBinds addXs (Place ty tmp) (CtorValH (Ctor c') ts' xs))

-- basically a concat + snoc for adding value binds
addManyBinds :: [TermH -> TermH] -> Place -> ValueH -> (TermH -> TermH)
addManyBinds addBinds x v = foldr (.) (\e' -> LetValH x v e') addBinds


freshId :: String -> HoistM Id
freshId x = do
  u <- freshUnique
  pure (Id x u)
