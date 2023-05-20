
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
import Control.Monad.State

import Data.Foldable (toList)
import Data.Function (on)
import Data.Functor.Identity
import Data.Functor.Compose
import Prelude hiding (cos)

import qualified CPS.IR as K
import CC.IR



data Context
  = Context {
    ctxTms :: Map K.TmVar (Name, Sort)
  , ctxCos :: Map K.CoVar (Name, Sort)
  , ctxTys :: Map K.TyVar (TyVar, Kind)
  }

emptyContext :: Context
emptyContext = Context Map.empty Map.empty Map.empty

data FreeOcc = FreeOcc { freeOccName :: Name, freeOccSort :: Sort }

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

singleOcc :: Name -> Sort -> Fields
singleOcc x s = Fields (Set.singleton (FreeOcc x s), Set.empty)

singleTyOcc :: TyVar -> Kind -> Fields
singleTyOcc aa k = Fields (Set.empty, Set.singleton (TyOcc aa k))

bindOccs :: Foldable t => t (Name, Sort) -> Fields -> Fields
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

insertMany :: Ord k => [(k, v)] -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

-- | Bind a sequence of term variables: both extending the typing context on
-- the way down, and removing them from the free variable set on the way back
-- up.
withTms :: Traversable t => t (K.TmVar, K.TypeK) -> (t (Name, Sort) -> ConvM a) -> ConvM a
withTms xs k = do
  xs' <- traverse (\ (x, t) -> cconvType t >>= \t' -> pure (x, (tmVar x, t'))) xs
  let bs = fmap snd xs'
  let extend (Context tms cos tys) = Context (insertMany (toList xs') tms) cos tys
  censor (bindOccs bs) $ local extend $ k bs
  where
    -- Hmm. I'm pretty sure I don't have to worry about shadowing, but I should
    -- double-check that.
    tmVar :: K.TmVar -> Name
    tmVar (K.TmVar x i) = Name x i

-- | Bind a sequence of coterm variables: both extending the typing context on
-- the way down, and removing them from the free variable set on the way back
-- up.
withCos :: Traversable t => t (K.CoVar, K.CoTypeK) -> (t (Name, Sort) -> ConvM a) -> ConvM a
withCos ks k = do
  ks' <- traverse (\ (x, t) -> cconvCoType t >>= \t' -> pure (x, (coVar x, t'))) ks
  let bs = fmap snd ks'
  let extend (Context tms cos tys) = Context tms (insertMany (toList ks') cos) tys
  censor (bindOccs bs) $ local extend $ k bs
  where
    -- Hmm. I'm pretty sure I don't have to worry about shadowing, but I should
    -- double-check that.
    coVar :: K.CoVar -> Name
    coVar (K.CoVar x i) = Name x i

-- | Bind a sequence of type variables: both extending the typing context on
-- the way down, and removing them from the free variable set on the way back
-- up.
withTys :: [(K.TyVar, K.KindK)] -> ([(TyVar, Kind)] -> ConvM a) -> ConvM a
withTys aas k = do
  aas' <- traverse (\ (aa, ki) -> cconvKind ki >>= \ki' -> pure (aa, (tyVar aa, ki'))) aas
  let bs = fmap snd aas'
  let extend (Context tms cos tys) = Context tms cos (insertMany aas' tys)
  censor (bindTys bs) $ local extend $ k bs
  where
    -- Hmm. I'm pretty sure I don't have to worry about shadowing, but I should
    -- double-check that.
    tyVar :: K.TyVar -> TyVar
    tyVar (K.TyVar aa i) = TyVar (aa ++ show i)

-- | A special case of 'withTms', for binding a single term variable.
withTm :: (K.TmVar, K.TypeK) -> ((Name, Sort) -> ConvM a) -> ConvM a
withTm b k = withTms (Identity b) (k . runIdentity)


cconvProgram :: K.Program -> Program
cconvProgram (K.Program ds e) = runConv $ do
  ds' <- traverse cconvDataDecl ds
  e' <- cconv e
  pure (Program ds' e')
  where
    runConv = fst . runWriter . flip runReaderT emptyContext . runConvM

cconvDataDecl :: K.DataDecl -> ConvM DataDecl
cconvDataDecl (K.DataDecl (K.TyCon tc) params ctors) =
  withTys params $ \params' -> do
    ctors' <- traverse cconvCtorDecl ctors
    pure (DataDecl (TyCon tc) params' ctors')

cconvCtorDecl :: K.CtorDecl -> ConvM CtorDecl
cconvCtorDecl (K.CtorDecl (K.Ctor c) args) = CtorDecl (Ctor c) <$> traverse cconvType args

cconvType :: K.TypeK -> ConvM Sort
cconvType (K.TyVarOccK aa) = Alloc <$> cconvTyVar aa
cconvType (K.AllK aas ss) = do
  withTys aas $ \aas' -> do
    ss' <- traverse cconvCoType ss
    let tele = map (uncurry TypeTele) aas' ++ map ValueTele ss'
    pure (Closure tele)
cconvType K.UnitK = pure Unit
cconvType K.TokenK = pure Token
cconvType K.IntK = pure Integer
cconvType K.BoolK = pure Boolean
cconvType K.StringK = pure String
cconvType K.CharK = pure Character
cconvType (K.ProdK t1 t2) = Pair <$> cconvType t1 <*> cconvType t2
cconvType (K.RecordK fields) = Record <$> traverse cconvField fields
  where cconvField (f, t) = (,) <$> cconvFieldLabel f <*> cconvType t
cconvType (K.FunK ts ss) = f <$> traverse cconvType ts <*> traverse cconvCoType ss
  where f ts' ss' = Closure (map ValueTele ts' ++ map ValueTele ss')
cconvType (K.TyConOccK (K.TyCon tc)) = pure (TyConOcc (TyCon tc))
cconvType (K.TyAppK t1 t2) = TyApp <$> cconvType t1 <*> cconvType t2

cconvCoType :: K.CoTypeK -> ConvM Sort
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
cconv (K.HaltK x) = HaltC <$> cconvTmVar x
cconv (K.JumpK k xs) = do
  (kbinds, Identity k') <- cconvCoArgs (Identity (K.CoVarK k))
  xs' <- traverse cconvTmVar xs
  let term = JumpC k' xs'
  if null kbinds then
    pure term
  else
    pure (LetContC kbinds term)
cconv (K.CallK f xs ks) = do
  f' <- cconvTmVar f
  xs' <- traverse (fmap ValueArg . cconvTmVar) xs
  (kbinds, ks') <- cconvCoArgs ks
  let term = (CallC f' xs' ks')
  if null kbinds then
    pure term
  else
    pure (LetContC kbinds term)
cconv (K.InstK f ts ks) = do
  f' <- cconvTmVar f
  ts' <- traverse (fmap TypeArg . cconvType) ts
  (kbinds, ks') <- cconvCoArgs ks
  let term = CallC f' ts' ks'
  if null kbinds then
    pure term
  else
    pure (LetContC kbinds term)
cconv (K.IfK x contf contt) = do
  x' <- cconvTmVar x
  contf' <- cconvContDef contf
  contt' <- cconvContDef contt
  let k1 = Name "__false_cont" 0
  let k2 = Name "__true_cont" 0
  let kbinds = [(k1, contf'), (k2, contt')]
  pure (LetContC kbinds (IfC x' k1 k2))
cconv (K.CaseK x kind ks) = do
  x' <- cconvTmVar x
  kind' <- cconvTyConApp kind
  -- Not quite the same as CallK/InstK because each co-"argument" is paired
  -- with a constructor (and the constructor also needs to be translated)
  (kbinds, ks0') <- cconvCoArgs (Compose ks)
  let ks' = map (\ (K.Ctor c, k') -> (Ctor c, k')) (getCompose ks0')
  let term = CaseC x' kind' ks'
  if null kbinds then
    pure term
  else
    pure (LetContC kbinds term)
-- Hmm. Technically, this is incorrect scoping.
-- x : T should not be in scope when translating the arguments to the operation.
cconv (K.LetFstK x t y e) = withTm (x, t) $ \b -> LetFstC b <$> cconvTmVar y <*> cconv e
cconv (K.LetSndK x t y e) = withTm (x, t) $ \b -> LetSndC b <$> cconvTmVar y <*> cconv e
cconv (K.LetFieldK x t y f e) = withTm (x, t) $ \b -> LetFieldC b <$> cconvTmVar y <*> cconvFieldLabel f <*> cconv e
cconv (K.LetValK x t v e) = withTm (x, t) $ \b -> LetValC b <$> cconvValue v <*> cconv e
cconv (K.LetArithK x op e) = withTm (x, K.IntK) $ \b -> LetArithC b <$> cconvArith op <*> cconv e
cconv (K.LetCompareK x op e) = withTm (x, K.BoolK) $ \b -> LetCompareC b <$> cconvCmp op <*> cconv e
cconv (K.LetStringOpK x t op e) = withTm (x, t) $ \b -> LetStringOpC b <$> cconvStringOp op <*> cconv e
cconv (K.LetBindK x y prim e) = do
  (prim', ansTy) <- cconvPrimIO prim
  withTm (x, K.TokenK) $ \b1 -> withTm (y, ansTy) $ \b2 ->
    LetBindC b1 b2 prim' <$> cconv e
cconv (K.LetFunAbsK fs e) = do
  let funBinds = map (\f -> (K.funDefName f, K.funDefType f)) fs
  withTms funBinds $ \_ -> LetFunC <$> traverse cconvFunDef fs <*> cconv e
cconv (K.LetContK ks e) = do
  let contBinds = map (\ (k, cont) -> (k, K.contDefType cont)) ks
  let contName (K.CoVar x i) = Name x i
  let cconvContBind (k, cont) = (,) (contName k) <$> cconvContDef cont
  withCos contBinds $ \_ -> LetContC <$> traverse cconvContBind ks <*> cconv e

cconvFunDef :: K.FunDef -> ConvM FunClosureDef
cconvFunDef (K.FunDef f xs ks e) = do
  ((params', e'), flds) <- listen $
    withTms xs $ \xs' -> do
      withCos ks $ \ks' -> do
        e' <- cconv e
        pure (makeClosureParams [] (xs' ++ ks'), e')
  env <- makeClosureEnv flds
  let fnName (K.TmVar x i) = Name x i
  pure (FunClosureDef (fnName f) env params' e')
cconvFunDef (K.AbsDef f as ks e) = do
  ((params', e'), flds) <- listen $
    withTys as $ \as' -> do
      withCos ks $ \ks' -> do
        e' <- cconv e
        pure (makeClosureParams as' ks', e')
  env <- makeClosureEnv flds
  let fnName (K.TmVar x i) = Name x i
  pure (FunClosureDef (fnName f) env params' e')

cconvContDef :: (K.ContDef) -> ConvM (ContClosureDef)
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
    ftv :: Map TyVar Kind -> Sort -> Set TyOcc
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
cconvValue K.NilK = pure NilC
cconvValue K.WorldTokenK = pure WorldTokenC
cconvValue (K.PairK x y) = PairC <$> cconvTmVar x <*> cconvTmVar y
cconvValue (K.RecordValK fs) = RecordC <$> traverse cconvField fs
  where cconvField (f, x) = (,) <$> cconvFieldLabel f <*> cconvTmVar x
cconvValue (K.IntValK i) = pure (IntC i)
cconvValue (K.BoolValK b) = pure (BoolC b)
cconvValue (K.StringValK s) = pure (StringC s)
cconvValue (K.CharValK s) = pure (CharC s)
cconvValue (K.CtorAppK (K.Ctor c) args) = CtorAppC (Ctor c) <$> traverse cconvTmVar args

cconvArith :: K.ArithK -> ConvM ArithC
cconvArith (K.AddK x y) = AddC <$> cconvTmVar x <*> cconvTmVar y
cconvArith (K.SubK x y) = SubC <$> cconvTmVar x <*> cconvTmVar y
cconvArith (K.MulK x y) = MulC <$> cconvTmVar x <*> cconvTmVar y
cconvArith (K.NegK x) = NegC <$> cconvTmVar x

cconvCmp :: K.CmpK -> ConvM CmpC
cconvCmp (K.CmpEqK x y) = EqC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (K.CmpNeK x y) = NeC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (K.CmpLtK x y) = LtC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (K.CmpLeK x y) = LeC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (K.CmpGtK x y) = GtC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (K.CmpGeK x y) = GeC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (K.CmpEqCharK x y) = EqCharC <$> cconvTmVar x <*> cconvTmVar y

cconvStringOp :: K.StringOpK -> ConvM StringOpC
cconvStringOp (K.ConcatK x y) = ConcatC <$> cconvTmVar x <*> cconvTmVar y
cconvStringOp (K.IndexK x y) = IndexC <$> cconvTmVar x <*> cconvTmVar y

cconvPrimIO :: K.PrimIO -> ConvM (PrimIO, K.TypeK)
cconvPrimIO (K.PrimGetLine x) =
  (\x' -> (GetLineC x', K.StringK)) <$> cconvTmVar x
cconvPrimIO (K.PrimPutLine x y) =
  (\x' y' -> (PutLineC x' y', K.UnitK)) <$> cconvTmVar x <*> cconvTmVar y


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

cconvCoArgs :: Traversable t => t K.CoValueK -> ConvM ([(Name, ContClosureDef)], t Name)
cconvCoArgs ks = do
  (args, (_, defs)) <- runStateT (traverse (StateT . f) ks) (0, [])
  pure (defs, args)
  where
    -- Already a variable. Don't need to bind a definition, just convert it.
    f (K.CoVarK k) (i, defs) = (\k' -> (k', (i, defs))) <$> cconvCoVar k
    -- Need to generate a name for the cont, convert the cont, etc.
    f (K.ContValK cont) (i, defs) = do
      let k' = Name "__anon_cont" i
      cont' <- cconvContDef cont
      pure (k', (i+1, (k', cont'):defs))

cconvTyVar :: K.TyVar -> ConvM TyVar
cconvTyVar aa = do
  tys <- asks ctxTys
  case Map.lookup aa tys of
    Nothing -> error ("type variable not in scope: " ++ show aa)
    Just (aa', k) -> writer (aa', singleTyOcc aa' k)


cconvFieldLabel :: K.FieldLabel -> ConvM FieldLabel
cconvFieldLabel (K.FieldLabel f) = pure (FieldLabel f)


