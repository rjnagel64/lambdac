
-- | A module describing the structure and syntactic operations on the Lower IR.
module Backend.Lower
    ( lowerProgram
    ) where

import qualified Data.Map as Map
import Data.Map (Map)

import Data.Maybe (catMaybes)
import Data.Traversable (for)

import qualified Hoist.IR as H
import Backend.IR

import Control.Monad.Reader
import Control.Monad.State


insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs


lowerProgram :: H.Program -> Program
lowerProgram (H.Program ds e) = runM $ do
  lowerDecls ds $ \ds' -> do
    e' <- lowerTerm e
    pure (Program ds' e')

-- Lower a sequence of declarations, where each declaration is in scope for all
-- subsequent ones.
lowerDecls :: [H.Decl] -> ([Decl] -> M a) -> M a
lowerDecls [] k = k []
lowerDecls (H.DeclData dd : ds) k = do
  withDataDecl dd $ \dd' -> do
    lowerDecls ds $ \ds' -> do
      k (DeclData dd' : ds')
lowerDecls (H.DeclCode cd : ds) k = do
  withCodeDecl cd $ \ed' cd' -> do
    lowerDecls ds $ \ds' -> do
      k (DeclEnv ed' : DeclCode cd' : ds')

withCodeDecl :: H.CodeDecl -> (EnvDecl -> CodeDecl -> M a) -> M a
withCodeDecl (H.CodeDecl l (envName, envDecl) params body) k = do
  withCodeLabel l $ \l' envTyCon -> do
    (ed', cd') <- do
      withEnvironment (envName, envDecl) $ \aas' envName' fields' -> do
        withParams params $ \params' -> do
          body' <- lowerTerm body
          let envd = EnvDecl envTyCon fields'
          let coded = CodeDecl l' aas' (envName', envTyCon) params' body'
          pure (envd, coded)
    k ed' cd'

withEnvironment :: (H.Id, H.EnvDecl) -> ([(TyVar, Kind)] -> Id -> [(FieldLabel, Type)] -> M a) -> M a
withEnvironment (envName, H.EnvDecl aas fields) k = do
  withTyVars aas $ \aas' -> do
    withEnvPtr envName $ \envName' -> do
      withEnvFields envName' fields $ \fields' -> do
        k aas' envName' fields'

withEnvFields :: Id -> [(H.FieldLabel, H.Type)] -> ([(FieldLabel, Type)] -> M a) -> M a
withEnvFields envp fields k = do
  (fields', binds, thunkBindsMaybe) <- fmap unzip3 $ for fields $ \ (x, s) -> do
    x' <- lowerFieldLabel x
    s' <- lowerType s
    let field' = (x', s')
    let bind = (H.EnvName x, EnvName envp x')
    case s' of
      ClosureH tele -> do
        let thunkBind = (H.EnvName x, teleThunkType tele)
        pure (field', bind, Just thunkBind)
      _ -> do
        pure (field', bind, Nothing)
  let thunkBinds = catMaybes thunkBindsMaybe
  let extend env = env { envNames = insertMany binds (envNames env), envThunkTypes = insertMany thunkBinds (envThunkTypes env) }
  local extend $ k fields'

withDataDecl :: H.DataDecl -> (DataDecl -> M a) -> M a
withDataDecl (H.DataDecl tc ki cds) k = do
  withTyCon tc $ \tc' -> do
    withCtorDecls tc' (zip [0..] cds) $ \cds' -> do
      k (DataDecl tc' cds')

withCtorDecls :: TyCon -> [(Int, H.CtorDecl)] -> ([CtorDecl] -> M a) -> M a
withCtorDecls _ [] k = k []
withCtorDecls tc' (cd : cds) k =
  withCtorDecl tc' cd $ \cd' -> do
    withCtorDecls tc' cds $ \cds' -> do
      k (cd' : cds')

withCtorDecl :: TyCon -> (Int, H.CtorDecl) -> (CtorDecl -> M a) -> M a
withCtorDecl tc' (i, H.CtorDecl c tys xs) k = do
  withCtor tc' i c $ \c' -> do
    cd <- withTyVars tys $ \tys' -> do
      xs' <- traverse makeField (zip [0..] xs)
      pure (CtorDecl c' tys' xs')
    k cd
    where
      makeField :: (Int, H.Type) -> M (FieldLabel, Type)
      makeField (j, s) = do
        s' <- lowerType s
        pure (FieldLabel ("arg" ++ show j), s')

lowerCodeLabel :: H.CodeLabel -> M GlobalLabel
lowerCodeLabel l = do
  env <- asks envCodeLabels
  case Map.lookup l env of
    Nothing -> error ("code label not in scope: " ++ show l)
    Just l' -> pure l'

lookupEnvTyCon :: H.CodeLabel -> M TyCon
lookupEnvTyCon l = do
  env <- asks envEnvTyCons
  case Map.lookup l env of
    Nothing -> error ("env tycon for " ++ show l ++ " not in scope")
    Just tc -> pure tc

lowerFieldLabel :: H.FieldLabel -> M FieldLabel
lowerFieldLabel (H.FieldLabel f) = pure (FieldLabel f)

lowerTerm :: H.TermH -> M TermH
lowerTerm (H.HaltH s x) = HaltH <$> lowerType s <*> lowerName x
lowerTerm (H.OpenH f xs) =
  OpenH <$> lookupThunkType f <*> lowerName f <*> traverse lowerClosureArg xs
lowerTerm (H.IfH x k1 k2) = do
  x' <- lowerName x
  alt1 <- IntCaseAlt 0 <$> lookupThunkType k1 <*> lowerName k1
  alt2 <- IntCaseAlt 1 <$> lookupThunkType k2 <*> lowerName k2
  pure (IntCaseH x' [alt1, alt2])
lowerTerm (H.CaseH x tcapp ks) = do
  CaseH <$> lowerName x <*> lowerTyConApp tcapp <*> traverse lowerCaseAlt ks
lowerTerm (H.LetValH p v e) = do
  v' <- lowerValue v
  withPlace p $ \p' -> do
    e' <- lowerTerm e
    pure (LetValH p' v' e')
lowerTerm (H.LetPrimH p op e) = do
  op' <- lowerPrimOp op
  withPlace p $ \p' -> do
    e' <- lowerTerm e
    pure (LetPrimH p' op' e')
lowerTerm (H.LetBindH ps px op e) = do
  op' <- lowerIOPrimOp op
  withPlace ps $ \ps' -> do
    withPlace px $ \px' -> do
      e' <- lowerTerm e
      pure (LetBindH ps' px' op' e')
lowerTerm (H.LetProjectH p x proj e) = do
  x' <- lowerName x
  proj' <- lowerProjection proj
  withPlace p $ \p' -> do
    e' <- lowerTerm e
    pure (LetProjectH p' x' proj' e')
lowerTerm (H.AllocClosure cs e) = do
  lowerClosureAllocs cs e

lowerClosureArg :: H.ClosureArg -> M ClosureArg
lowerClosureArg (H.ValueArg x) = ValueArg <$> lowerName x
lowerClosureArg (H.TypeArg s) = TypeArg <$> lowerType s

lowerProjection :: H.Projection -> M Projection
lowerProjection H.ProjectFst = pure ProjectFst
lowerProjection H.ProjectSnd = pure ProjectSnd
lowerProjection (H.ProjectField f) = ProjectField <$> lowerFieldLabel f

lowerValue :: H.ValueH -> M ValueH
lowerValue (H.IntValH i) = pure (IntH i)
lowerValue (H.BoolValH b) = pure (BoolH b)
lowerValue (H.StringValH s) = pure (StringValH s)
lowerValue (H.CharValH c) = pure (CharValH c)
lowerValue (H.PairValH x y) = PairH <$> lowerName x <*> lowerName y
lowerValue H.NilValH = pure NilH
lowerValue H.TokenValH = pure WorldToken
lowerValue (H.RecordValH fields) = RecordH <$> traverse lowerField fields
  where lowerField (f, x) = (,) <$> lowerFieldLabel f <*> lowerName x
lowerValue (H.CtorValH c ss xs) = 
  CtorAppH <$> lowerCtor c <*> traverse lowerType ss <*> traverse lowerName xs

lowerTyConApp :: H.TyConApp -> M TyConApp
lowerTyConApp (H.TyConApp tc ss) = TyConApp <$> lowerTyCon tc <*> traverse lowerType ss

lowerPrimOp :: H.PrimOp -> M PrimOp
lowerPrimOp (H.PrimAddInt64 x y) = PrimAddInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimSubInt64 x y) = PrimSubInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimMulInt64 x y) = PrimMulInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimNegInt64 x) = PrimNegInt64 <$> lowerName x
lowerPrimOp (H.PrimEqInt64 x y) = PrimEqInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimNeInt64 x y) = PrimNeInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimLtInt64 x y) = PrimLtInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimLeInt64 x y) = PrimLeInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimGeInt64 x y) = PrimGtInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimGtInt64 x y) = PrimGeInt64 <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimEqChar x y) = PrimEqChar <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimConcatenate x y) = PrimConcatenate <$> lowerName x <*> lowerName y
lowerPrimOp (H.PrimStrlen x) = PrimStrlen <$> lowerName x
lowerPrimOp (H.PrimIndexStr x y) = PrimIndexStr <$> lowerName x <*> lowerName y

lowerIOPrimOp :: H.PrimIO -> M PrimIO
lowerIOPrimOp (H.PrimGetLine x) = PrimGetLine <$> lowerName x
lowerIOPrimOp (H.PrimPutLine x y) = PrimPutLine <$> lowerName x <*> lowerName y

lowerCaseAlt :: (H.Ctor, H.Name) -> M CaseAlt
lowerCaseAlt (c, k) = CaseAlt <$> lowerCtor c <*> lookupThunkType k <*> lowerName k

lowerClosureAllocs :: [H.ClosureAlloc] -> H.TermH -> M TermH
lowerClosureAllocs cs e = do
  -- forward-declare the closures (thunk type and name mapping) and environments
  (pcs, xbinds, thbinds) <- fmap unzip3 $ for cs $ \ cl@(H.ClosureAlloc (H.Place s x) l _envp _enva) -> do
    x' <- freshenId' x
    s' <- lowerType s
    let p' = Place s' x'
    l' <- lowerCodeLabel l
    tc <- lookupEnvTyCon l
    let (occ, occ') = (H.LocalName x, LocalName x')
    thunkTy <- case s' of
      ClosureH tele -> pure (teleThunkType tele)
      _ -> error "closure place must have closure type"
    pure ((p', l', tc, cl), (occ, occ'), (occ, thunkTy))

  let
    extend env = env {
        envNames = insertMany xbinds (envNames env)
      , envThunkTypes = insertMany thbinds (envThunkTypes env)
      }
  (es', cs', e') <- local extend $ do
    -- lower each individual alloc in an extended environment
    (cs', es') <- fmap unzip $ for pcs $ \ (p', l', tc, H.ClosureAlloc _ _ envp (H.EnvAlloc tys xs)) -> do
      envp' <- freshenId' envp
      tys' <- traverse lowerType tys
      xs' <- traverse (\ (fld, x) -> (,) <$> lowerFieldLabel fld <*> lowerName x) xs
      let enva = EnvAlloc envp' tc xs'
      let closa = ClosureAlloc p' l' tys' envp'
      pure (closa, enva)

    -- lower the body in the extended environment
    e' <- lowerTerm e
    pure (es', cs', e')

  pure (AllocClosures es' cs' e')

lowerType :: H.Type -> M Type
lowerType (H.AllocH aa) = AllocH <$> lowerTyVar aa
lowerType H.IntegerH = pure IntegerH
lowerType H.BooleanH = pure BooleanH
lowerType H.UnitH = pure UnitH
lowerType H.StringH = pure StringH
lowerType H.CharH = pure CharH
lowerType (H.ProductH t s) = ProductH <$> lowerType t <*> lowerType s
lowerType (H.ClosureH tele) = ClosureH <$> lowerClosureTele tele
lowerType (H.RecordH fields) = TyRecordH <$> traverse lowerField fields
  where lowerField (f, t) = (,) <$> lowerFieldLabel f <*> lowerType t
lowerType (H.TyConH tc) = TyConH <$> lowerTyCon tc
lowerType (H.TyAppH t s) = TyAppH <$> lowerType t <*> lowerType s
lowerType H.TokenH = pure TokenH

lowerClosureTele :: H.ClosureTele -> M ClosureTele
lowerClosureTele (H.ClosureTele tele) = withTele tele $ \tele' -> pure (ClosureTele tele')

withTele :: [H.TeleEntry] -> ([TeleEntry] -> M a) -> M a
withTele [] k = k []
withTele (H.ValueTele s : tele) k = do
  s' <- lowerType s
  withTele tele $ \tele' -> k (ValueTele s' : tele')
withTele (H.TypeTele aa kk : tele) k =
  withTyVar aa kk $ \aa' kk' ->
    withTele tele $ \tele' -> k (TypeTele aa' kk' : tele')

lowerKind :: H.Kind -> M Kind
lowerKind H.Star = pure Star
lowerKind (H.KArr k1 k2) = KArr <$> lowerKind k1 <*> lowerKind k2

-- Lower an occurrence of a name: either a local reference or an environment
-- reference.
lowerName :: H.Name -> M Name
lowerName x = do
  env <- asks envNames
  case Map.lookup x env of
    Nothing -> error "name not in scope"
    Just x' -> pure x'

-- Lower an occurrence of a type variable.
lowerTyVar :: H.TyVar -> M TyVar
lowerTyVar aa = do
  env <- asks envTyVars
  case Map.lookup aa env of
    Nothing -> error "tyvar not in scope"
    Just aa' -> pure aa'

lowerCtor :: H.Ctor -> M Ctor
lowerCtor c = do
  env <- asks envCtors
  case Map.lookup c env of
    Nothing -> error ("lowerCtor: ctor not in scope: " ++ show c)
    Just c' -> pure c'

lowerTyCon :: H.TyCon -> M TyCon
lowerTyCon tc = do
  env <- asks envTyCons
  case Map.lookup tc env of
    Nothing -> error "tycon not in scope"
    Just tc' -> pure tc'

newtype M a = M { getM :: StateT Unique (Reader LowerEnv) a }
deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader LowerEnv M
deriving newtype instance MonadState Unique M

data LowerEnv
  = LowerEnv {
    envNames :: Map H.Name Name
  , envTyVars :: Map H.TyVar TyVar
  , envTyCons :: Map H.TyCon TyCon
  , envCtors :: Map H.Ctor Ctor
  , envThunkTypes :: Map H.Name ThunkType
  , envCodeLabels :: Map H.CodeLabel GlobalLabel
  , envEnvTyCons :: Map H.CodeLabel TyCon
  }

runM :: M a -> a
runM = flip runReader emptyEnv . flip evalStateT (Unique 0) . getM
  where
    emptyEnv = LowerEnv {
        envNames = Map.empty
      , envTyVars = Map.empty
      , envTyCons = Map.empty
      , envCtors = Map.empty
      , envThunkTypes = Map.empty
      , envCodeLabels = Map.empty
      , envEnvTyCons = Map.empty
      }

withEnvPtr :: H.Id -> (Id -> M a) -> M a
withEnvPtr envp k = do
  envp' <- freshenId' envp
  k envp'

-- Problem: this needs to be in scope for all subsequent closures, not just the
-- body of the current closure. Think about how to do this.
withCodeLabel :: H.CodeLabel -> (GlobalLabel -> TyCon -> M a) -> M a
withCodeLabel l@(H.CodeLabel x (H.Unique u)) k = do
  let l' = GlobalLabel x u -- TODO: Why do I not generate a new unique here?
  let envTyCon = TyCon ("env_" ++ show u)
  let extend env = env { envCodeLabels = Map.insert l l' (envCodeLabels env), envEnvTyCons = Map.insert l envTyCon (envEnvTyCons env) }
  local extend $ k l' envTyCon

withParams :: [H.ClosureParam] -> ([ClosureParam] -> M a) -> M a
withParams [] k = k []
withParams (H.PlaceParam p : ps) k =
  withPlace p $ \p' -> withParams ps (\ps' -> k (PlaceParam p':ps'))
withParams (H.TypeParam aa kk : ps) k =
  withTyVar aa kk $ \aa' kk' -> withParams ps (\ps' -> k (TypeParam aa' kk':ps'))

withPlace :: H.Place -> (Place -> M a) -> M a
withPlace (H.Place s x) k = do
  s' <- lowerType s
  x' <- freshenId' x
  let (occ, occ') = (H.LocalName x, LocalName x')
  -- Occurrences of the Hoist name 'occ' will be mapped to occurrences of the
  -- new Lower name 'occ''.
  let extendNames env = env { envNames = Map.insert occ occ' (envNames env) }
  -- Places that have a closure type are associated with a Thunk Type: the
  -- calling convention used to invoke that closure.
  let
    extendThunk env = case s' of
      ClosureH tele ->
        env { envThunkTypes = Map.insert occ (teleThunkType tele) (envThunkTypes env) }
      _ -> env
  local (extendNames . extendThunk) $ k (Place s' x')

freshUnique :: M Unique
freshUnique = do
  u <- get
  modify' (\ (Unique u) -> Unique (u+1))
  pure u

freshenId' :: H.Id -> M Id
freshenId' (H.Id x _u) = do
  u <- freshUnique
  pure (Id x u)

withTyVar :: H.TyVar -> H.Kind -> (TyVar -> Kind -> M a) -> M a
withTyVar aa@(H.TyVar x i) kk k = do
  let aa' = TyVar x i
  kk' <- lowerKind kk
  let extend env = env { envTyVars = Map.insert aa aa' (envTyVars env) }
  local extend $ k aa' kk'

withTyVars :: [(H.TyVar, H.Kind)] -> ([(TyVar, Kind)] -> M a) -> M a
withTyVars [] k = k []
withTyVars ((aa, kk):tys) k =
  withTyVar aa kk $ \aa' kk' ->
    withTyVars tys $ \tys' ->
      k ((aa', kk'):tys')

withTyCon :: H.TyCon -> (TyCon -> M a) -> M a
withTyCon tc@(H.TyCon x) k = do
  let tc' = TyCon x
  let extend env = env { envTyCons = Map.insert tc tc' (envTyCons env) }
  local extend $ k tc'

withCtor :: TyCon -> Int -> H.Ctor -> (Ctor -> M a) -> M a
withCtor tc' i c@(H.Ctor x) k = do
  let c' = Ctor tc' x i
  let extend env = env { envCtors = Map.insert c c' (envCtors env) }
  local extend $ k c'

lookupThunkType :: H.Name -> M ThunkType
lookupThunkType x = do
  env <- asks envThunkTypes
  case Map.lookup x env of
    Nothing -> error "calling convention missing for variable"
    Just ty -> pure ty



