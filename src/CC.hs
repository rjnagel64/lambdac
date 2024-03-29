
module CC
    ( cconvProgram
    , pprintProgram
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer

import Data.Foldable (toList)
import Data.Function (on)
import Data.Functor.Identity
import Prelude hiding (cos)

import qualified CPS.IR as K
import CC.IR
import Util



data Context
  = Context {
    ctxTms :: Map K.TmVar (Name, Type)
  , ctxCos :: Map K.CoVar (Name, Type)
  , ctxTys :: Map K.TyVar (TyVar, Kind)
  }

emptyContext :: Context
emptyContext = Context Map.empty Map.empty Map.empty

data FreeOcc = FreeOcc { freeOccName :: Name, freeOccType :: Type }

instance Eq FreeOcc where
  (==) = (==) `on` freeOccName

instance Ord FreeOcc where
  compare = compare `on` freeOccName

data TyOcc = TyOcc { tyOccName :: TyVar, tyOccKind :: Kind }

instance Eq TyOcc where
  (==) = (==) `on` tyOccName

instance Ord TyOcc where
  compare = compare `on` tyOccName

newtype Fields = Fields { getFields :: (Set FreeOcc, Set TyOcc) }

instance Semigroup Fields where
  f <> g = Fields $ getFields f <> getFields g

instance Monoid Fields where
  mempty = Fields (Set.empty, Set.empty)

singleOcc :: Name -> Type -> Fields
singleOcc x s = Fields (Set.singleton (FreeOcc x s), Set.empty)

singleTyOcc :: TyVar -> Kind -> Fields
singleTyOcc aa k = Fields (Set.empty, Set.singleton (TyOcc aa k))

bindOccs :: Foldable t => t (Name, Type) -> Fields -> Fields
bindOccs bs flds =
  let (occs, tys) = getFields flds in
  let bound = Set.fromList $ fmap (uncurry FreeOcc) (toList bs) in
  Fields (occs Set.\\ bound, tys)

bindTys :: Foldable t => t (TyVar, Kind) -> Fields -> Fields
bindTys aas flds =
  let (occs, tys) = getFields flds in
  let bound = Set.fromList $ fmap (uncurry TyOcc) (toList aas) in
  Fields (occs, tys Set.\\ bound)

-- Hmm. Should probably add 'StateT Int' in order to generate names for
-- anonymous continuations. 'let __anon5 : (...) -> ! = cont(...) => e; in ...'
-- probably won't cause name collisions.
newtype ConvM a = ConvM { runConvM :: ReaderT Context (Writer Fields) a }

deriving instance Functor ConvM
deriving instance Applicative ConvM
deriving instance Monad ConvM

deriving instance MonadReader Context ConvM
deriving instance MonadWriter Fields ConvM

-- | Bind a sequence of term variables: both extending the typing context on
-- the way down, and removing them from the free variable set on the way back
-- up.
withTms :: Traversable t => t (K.TmVar, K.TypeK) -> (t (Name, Type) -> ConvM a) -> ConvM a
withTms xs k = do
  xs' <- traverse (\ (x, t) -> cconvType t >>= \t' -> pure (x, (tmVar x, t'))) xs
  let bs = fmap snd xs'
  let extend (Context tms cos tys) = Context (insertMany xs' tms) cos tys
  censor (bindOccs bs) $ local extend $ k bs
  where
    -- Hmm. I'm pretty sure I don't have to worry about shadowing, but I should
    -- double-check that.
    tmVar :: K.TmVar -> Name
    tmVar (K.TmVar x i) = Name x i

-- | Bind a sequence of coterm variables: both extending the typing context on
-- the way down, and removing them from the free variable set on the way back
-- up.
withCos :: Traversable t => t (K.CoVar, K.CoTypeK) -> (t (Name, Type) -> ConvM a) -> ConvM a
withCos ks k = do
  ks' <- traverse (\ (x, t) -> cconvCoType t >>= \t' -> pure (x, (coVar x, t'))) ks
  let bs = fmap snd ks'
  let extend (Context tms cos tys) = Context tms (insertMany ks' cos) tys
  censor (bindOccs bs) $ local extend $ k bs
  where
    -- Hmm. I'm pretty sure I don't have to worry about shadowing, but I should
    -- double-check that.
    coVar :: K.CoVar -> Name
    coVar (K.CoVar x i) = Name x i

-- | Bind a sequence of type variables: both extending the typing context on
-- the way down, and removing them from the free variable set on the way back
-- up.
withTys :: Traversable t => t (K.TyVar, K.KindK) -> (t (TyVar, Kind) -> ConvM a) -> ConvM a
withTys aas k = do
  aas' <- traverse (\ (aa, ki) -> cconvKind ki >>= \ki' -> pure (aa, (tyVar aa, ki'))) aas
  let bs = fmap snd aas'
  let extend (Context tms cos tys) = Context tms cos (insertMany aas' tys)
  censor (bindTys bs) $ local extend $ k bs
  where
    -- Hmm. I'm pretty sure I don't have to worry about shadowing, but I should
    -- double-check that.
    tyVar :: K.TyVar -> TyVar
    tyVar (K.TyVar aa i) = TyVar aa i

-- | A special case of 'withTms', for binding a single term variable.
withTm :: (K.TmVar, K.TypeK) -> ((Name, Type) -> ConvM a) -> ConvM a
withTm b k = withTms (Identity b) (k . runIdentity)

withTy :: (K.TyVar, K.KindK) -> ((TyVar, Kind) -> ConvM a) -> ConvM a
withTy b k = withTys (Identity b) (k . runIdentity)


cconvProgram :: K.Program -> Program
cconvProgram (K.Program ds e) = runConv $ do
  ds' <- traverse cconvDataDecl ds
  e' <- cconv e
  pure (Program ds' e')
  where
    runConv = fst . runWriter . flip runReaderT emptyContext . runConvM

cconvDataDecl :: K.DataDecl -> ConvM DataDecl
cconvDataDecl (K.DataDecl (K.TyCon tc) kind ctors) = do
  kind' <- cconvKind kind
  ctors' <- traverse cconvCtorDecl ctors
  pure (DataDecl (TyCon tc) kind' ctors')

cconvCtorDecl :: K.CtorDecl -> ConvM CtorDecl
cconvCtorDecl (K.CtorDecl (K.Ctor c) params args) =
  withTys params $ \params' -> CtorDecl (Ctor c) params' <$> traverse cconvType args

cconvType :: K.TypeK -> ConvM Type
cconvType (K.TyVarOccK aa) = Alloc <$> cconvTyVar aa
cconvType K.UnitK = pure Unit
cconvType K.TokenK = pure Token
cconvType K.IntK = pure Integer
cconvType K.BoolK = pure Boolean
cconvType K.StringK = pure String
cconvType K.CharK = pure Character
cconvType (K.ProdK t1 t2) = Pair <$> cconvType t1 <*> cconvType t2
cconvType (K.RecordK fields) = Record <$> traverse cconvField fields
  where cconvField (f, t) = (,) <$> cconvFieldLabel f <*> cconvType t
cconvType (K.FunK tele ss) = withTypeTele tele $ \tele' -> do
  ss' <- traverse cconvCoType ss
  pure (Closure (tele' ++ map ValueTele ss'))
cconvType (K.TyConOccK (K.TyCon tc)) = pure (TyConOcc (TyCon tc))
cconvType (K.TyAppK t1 t2) = TyApp <$> cconvType t1 <*> cconvType t2

withTypeTele :: [K.TeleEntry] -> ([TeleEntry] -> ConvM a) -> ConvM a
withTypeTele [] cont = cont []
withTypeTele (K.ValueTele t : tele) cont = do
  t' <- cconvType t
  withTypeTele tele $ \tele' ->
    cont (ValueTele t' : tele')
withTypeTele (K.TypeTele aa k : tele) cont = do
  withTy (aa, k) $ \ (aa', k') ->
    withTypeTele tele $ \tele' ->
      cont (TypeTele aa' k' : tele')

cconvCoType :: K.CoTypeK -> ConvM Type
cconvCoType (K.ContK ss) = do
  ss' <- traverse cconvType ss
  let tele = map ValueTele ss'
  pure (Closure tele)

cconvKind :: K.KindK -> ConvM Kind
cconvKind K.StarK = pure Star
cconvKind (K.KArrK k1 k2) = KArr <$> cconvKind k1 <*> cconvKind k2

cconvTyConApp :: K.TyConApp -> ConvM TyConApp
cconvTyConApp (K.TyConApp (K.TyCon tc) args) = TyConApp (TyCon tc) <$> traverse cconvType args

cconv :: K.TermK -> ConvM TermC
cconv (K.HaltK x) = HaltC <$> cconvValue x
cconv (K.JumpK k xs) = do
  k' <- cconvCoValue k
  xs' <- traverse cconvValue xs
  pure (JumpC k' xs')
cconv (K.CallK f args ks) = do
  f' <- cconvValue f
  args' <- traverse cconvArgument args
  ks' <- traverse cconvCoValue ks
  pure (CallC f' args' ks')
cconv (K.IfK x contf contt) = do
  x' <- cconvValue x
  contf' <- cconvContDef contf
  contt' <- cconvContDef contt
  pure (IfC x' contf' contt')
cconv (K.CaseK x kind ks) = do
  x' <- cconvValue x
  kind' <- cconvTyConApp kind
  ks' <- traverse (\ (K.Ctor c, k) -> (,) <$> pure (Ctor c) <*> cconvCoValue k) ks
  pure (CaseC x' kind' ks')
cconv (K.LetFstK x t y e) = do
  y' <- cconvValue y
  withTm (x, t) $ \b -> LetFstC b y' <$> cconv e
cconv (K.LetSndK x t y e) = do
  y' <- cconvValue y
  withTm (x, t) $ \b -> LetSndC b y' <$> cconv e
cconv (K.LetFieldK x t y f e) = do
  y' <- cconvValue y
  f' <- cconvFieldLabel f
  withTm (x, t) $ \b -> LetFieldC b y' f' <$> cconv e
cconv (K.LetValK x t v e) = do
  v' <- cconvValue v
  withTm (x, t) $ \b -> LetValC b v' <$> cconv e
cconv (K.LetArithK x op e) = do
  op' <- cconvArith op
  withTm (x, K.IntK) $ \b -> LetArithC b op' <$> cconv e
cconv (K.LetCompareK x op e) = do
  op' <- cconvCmp op
  withTm (x, K.BoolK) $ \b -> LetCompareC b op' <$> cconv e
cconv (K.LetStringOpK x t op e) = do
  op' <- cconvStringOp op
  withTm (x, t) $ \b -> LetStringOpC b op' <$> cconv e
cconv (K.LetBindK x y prim e) = do
  (prim', ansTy) <- cconvPrimIO prim
  withTm (x, K.TokenK) $ \b1 -> withTm (y, ansTy) $ \b2 ->
    LetBindC b1 b2 prim' <$> cconv e
cconv (K.LetFunK fs e) = do
  let funBinds = map (\f -> (K.funDefName f, K.funDefType f)) fs
  withTms funBinds $ \_ -> LetFunC <$> traverse cconvFunDef fs <*> cconv e
cconv (K.LetContK ks e) = do
  let contBinds = map (\ (k, cont) -> (k, K.contDefType cont)) ks
  let contName (K.CoVar x i) = Name x i
  let cconvContBind (k, cont) = (,) (contName k) <$> cconvContDef cont
  withCos contBinds $ \_ -> LetContC <$> traverse cconvContBind ks <*> cconv e

cconvFunDef :: K.FunDef -> ConvM FunClosureDef
cconvFunDef (K.FunDef f params ks e) = do
  ((params', e'), flds) <- listen $
    withFunParams params $ \params' ->
      withCos ks $ \ks' -> do
        e' <- cconv e
        pure (params' ++ map (uncurry ValueParam) ks', e')
  env <- makeClosureEnv flds
  let fnName (K.TmVar x i) = Name x i
  pure (FunClosureDef (fnName f) env params' e')

withFunParams :: [K.FunParam] -> ([ClosureParam] -> ConvM a) -> ConvM a
withFunParams [] cont = cont []
withFunParams (K.ValueParam x t : params) cont =
  withTm (x, t) $ \ (x', t') ->
    withFunParams params $ \params' ->
      cont (ValueParam x' t' : params')
withFunParams (K.TypeParam aa k : params) cont =
  withTy (aa, k) $ \ (aa', k') ->
    withFunParams params $ \params' ->
      cont (TypeParam aa' k' : params')

cconvContDef :: K.ContDef -> ConvM (ContClosureDef)
cconvContDef (K.ContDef xs e) = do
  ((xs', e'), flds) <- listen $
    withTms xs $ \xs' -> do
      e' <- cconv e
      pure (xs', e')
  env <- makeClosureEnv flds
  pure (ContClosureDef env xs' e')

makeClosureEnv :: Fields -> ConvM EnvDef
makeClosureEnv flds = do
  let (fields, tyfields) = getFields flds
  -- The fields (x : s) bound in the environment may have free variables of their own.
  -- Gather those free variables and add them to the environment.
  ctx <- asks (Map.fromList . map snd . Map.toList . ctxTys)
  let (envFields, fieldTyOccs) = unzip $ map (\ (FreeOcc x s) -> ((x, s), ftv ctx s)) $ Set.toList fields
  let envTyFields = map (\ (TyOcc aa k) -> (aa, k)) $ Set.toList (Set.unions fieldTyOccs <> tyfields)
  pure (EnvDef envTyFields envFields)
  where
    -- This isn't terribly elegant, but it works.
    ftv :: Map TyVar Kind -> Type -> Set TyOcc
    ftv ctx (Alloc aa) = case Map.lookup aa ctx of
      Nothing -> error ("makeClosureEnv: not in scope: " ++ show aa)
      Just k -> Set.singleton (TyOcc aa k)
    ftv ctx (Closure tele) = go ctx Set.empty tele
      where
        go _ acc [] = acc
        go ctx' acc (ValueTele t : rest) = go ctx' (ftv ctx' t <> acc) rest
        go ctx' acc (TypeTele aa k : rest) =
          Set.delete (TyOcc aa k) $ go (Map.insert aa k ctx') acc rest
    ftv _ Integer = Set.empty
    ftv _ Unit = Set.empty
    ftv _ Boolean = Set.empty
    ftv _ String = Set.empty
    ftv _ Character = Set.empty
    ftv _ Token = Set.empty
    ftv _ (TyConOcc _) = Set.empty
    ftv ctx (Pair t1 t2) = ftv ctx t1 <> ftv ctx t2
    ftv ctx (Record fields) = foldMap (ftv ctx . snd) fields
    ftv ctx (TyApp t1 t2) = ftv ctx t1 <> ftv ctx t2


cconvValue :: K.ValueK -> ConvM ValueC
cconvValue (K.VarValK x) = VarValC <$> cconvTmVar x
cconvValue K.NilValK = pure NilValC
cconvValue K.TokenValK = pure TokenValC
cconvValue (K.PairValK x y) = PairValC <$> cconvValue x <*> cconvValue y
cconvValue (K.RecordValK fs) = RecordValC <$> traverse cconvField fs
  where cconvField (f, x) = (,) <$> cconvFieldLabel f <*> cconvValue x
cconvValue (K.IntValK i) = pure (IntValC i)
cconvValue (K.BoolValK b) = pure (BoolValC b)
cconvValue (K.StringValK s) = pure (StringValC s)
cconvValue (K.CharValK s) = pure (CharValC s)
cconvValue (K.CtorValK (K.Ctor c) tyargs args) =
  CtorValC (Ctor c) <$> traverse cconvType tyargs <*> traverse cconvValue args

cconvArith :: K.ArithK -> ConvM ArithC
cconvArith (K.AddK x y) = AddC <$> cconvValue x <*> cconvValue y
cconvArith (K.SubK x y) = SubC <$> cconvValue x <*> cconvValue y
cconvArith (K.MulK x y) = MulC <$> cconvValue x <*> cconvValue y
cconvArith (K.NegK x) = NegC <$> cconvValue x

cconvCmp :: K.CmpK -> ConvM CmpC
cconvCmp (K.CmpEqK x y) = EqC <$> cconvValue x <*> cconvValue y
cconvCmp (K.CmpNeK x y) = NeC <$> cconvValue x <*> cconvValue y
cconvCmp (K.CmpLtK x y) = LtC <$> cconvValue x <*> cconvValue y
cconvCmp (K.CmpLeK x y) = LeC <$> cconvValue x <*> cconvValue y
cconvCmp (K.CmpGtK x y) = GtC <$> cconvValue x <*> cconvValue y
cconvCmp (K.CmpGeK x y) = GeC <$> cconvValue x <*> cconvValue y
cconvCmp (K.CmpEqCharK x y) = EqCharC <$> cconvValue x <*> cconvValue y

cconvStringOp :: K.StringOpK -> ConvM StringOpC
cconvStringOp (K.ConcatK x y) = ConcatC <$> cconvValue x <*> cconvValue y
cconvStringOp (K.IndexK x y) = IndexC <$> cconvValue x <*> cconvValue y
cconvStringOp (K.LengthK x) = LengthC <$> cconvValue x

cconvPrimIO :: K.PrimIO -> ConvM (PrimIO, K.TypeK)
cconvPrimIO (K.PrimGetLine x) =
  (\x' -> (GetLineC x', K.StringK)) <$> cconvValue x
cconvPrimIO (K.PrimPutLine x y) =
  (\x' y' -> (PutLineC x' y', K.UnitK)) <$> cconvValue x <*> cconvValue y


cconvTmVar :: K.TmVar -> ConvM Name
cconvTmVar x = do
  tms <- asks ctxTms
  case Map.lookup x tms of
    Nothing -> error ("variable not in scope: " ++ show x)
    Just (x', s) -> writer (x', singleOcc x' s)

cconvCoVar :: K.CoVar -> ConvM Name
cconvCoVar x = do
  cos <- asks ctxCos
  case Map.lookup x cos of
    Nothing -> error ("variable not in scope: " ++ show x)
    Just (x', s) -> writer (x', singleOcc x' s)

cconvArgument :: K.Argument -> ConvM Argument
cconvArgument (K.ValueArg x) = ValueArg <$> cconvValue x
cconvArgument (K.TypeArg t) = TypeArg <$> cconvType t

cconvCoValue :: K.CoValueK -> ConvM CoValueC
cconvCoValue (K.CoVarK k) = VarCoVal <$> cconvCoVar k
cconvCoValue (K.ContValK cont) = ContCoVal <$> cconvContDef cont

cconvTyVar :: K.TyVar -> ConvM TyVar
cconvTyVar aa = do
  tys <- asks ctxTys
  case Map.lookup aa tys of
    Nothing -> error ("type variable not in scope: " ++ show aa)
    Just (aa', k) -> writer (aa', singleTyOcc aa' k)


cconvFieldLabel :: K.FieldLabel -> ConvM FieldLabel
cconvFieldLabel (K.FieldLabel f) = pure (FieldLabel f)


