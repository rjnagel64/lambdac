
module CC
    ( cconvProgram
    , pprintProgram
    ) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)

import Data.Foldable (toList)
import Data.Function (on)
import Data.Functor.Identity
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


cconvProgram :: K.Program a -> Program
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
cconvType K.IntK = pure Integer
cconvType K.BoolK = pure Boolean
cconvType K.StringK = pure String
cconvType (K.SumK t1 t2) = Sum <$> cconvType t1 <*> cconvType t2
cconvType (K.ProdK t1 t2) = Pair <$> cconvType t1 <*> cconvType t2
cconvType (K.ListK t) = List <$> cconvType t
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

asTyConApp :: Sort -> Maybe CaseKind
asTyConApp Boolean = Just CaseBool
asTyConApp (Sum a b) = Just (CaseSum a b)
asTyConApp (List a) = Just (CaseList a)
asTyConApp (TyConOcc tc) = Just (TyConApp tc [])
asTyConApp (TyApp a b) = go a [b]
  where
    go (TyApp a' b') args = go a' (b' : args)
    go (TyConOcc tc) args = Just (TyConApp tc args)
    go _ _ = Nothing
asTyConApp _ = Nothing

cconv :: K.TermK a -> ConvM TermC
cconv (K.HaltK x) = HaltC <$> cconvTmVar x
cconv (K.JumpK k xs) = JumpC <$> cconvCoVar k <*> traverse cconvTmVar xs
cconv (K.CallK f xs ks) =
  CallC <$> cconvTmVar f <*> traverse (fmap ValueArg . cconvTmVar) xs <*> traverse cconvCoVar ks
cconv (K.InstK f ts ks) =
  CallC <$> cconvTmVar f <*> traverse (fmap TypeArg . cconvType) ts <*> traverse cconvCoVar ks 
cconv (K.CaseK x t ks) = do
  x' <- cconvTmVar x
  kind <- fmap asTyConApp (cconvType t) >>= \case
    Nothing -> error "cannot perform case analysis on this type"
    Just tcapp -> pure tcapp
  ks' <- traverse (\ (K.Ctor c, k) -> (,) (Ctor c) <$> cconvCoVar k) ks
  pure (CaseC x' kind ks')
cconv (K.LetFstK x t y e) = withTm (x, t) $ \b -> LetFstC b <$> cconvTmVar y <*> cconv e
cconv (K.LetSndK x t y e) = withTm (x, t) $ \b -> LetSndC b <$> cconvTmVar y <*> cconv e
cconv (K.LetValK x t v e) = withTm (x, t) $ \b -> LetValC b <$> cconvValue v <*> cconv e
cconv (K.LetArithK x op e) = withTm (x, K.IntK) $ \b -> LetArithC b <$> cconvArith op <*> cconv e
cconv (K.LetCompareK x cmp e) = withTm (x, K.BoolK) $ \b -> LetCompareC b <$> cconvCmp cmp <*> cconv e
cconv (K.LetConcatK x y z e) =
  withTm (x, K.StringK) $ \b -> LetConcatC b <$> cconvTmVar y <*> cconvTmVar z <*> cconv e
cconv (K.LetFunAbsK fs e) = do
  let funBinds = map (\f -> (K.funDefName f, K.funDefType f)) fs
  withTms funBinds $ \_ -> LetFunC <$> traverse cconvFunDef fs <*> cconv e
cconv (K.LetContK ks e) = do
  let contBinds = map (\k -> (K.contDefName k, K.contDefType k)) ks
  withCos contBinds $ \_ -> LetContC <$> traverse cconvContDef ks <*> cconv e

cconvFunDef :: K.FunDef a -> ConvM FunClosureDef
cconvFunDef (K.FunDef _ f xs ks e) = do
  ((params', e'), flds) <- listen $
    withTms xs $ \xs' -> do
      withCos ks $ \ks' -> do
        e' <- cconv e
        pure (makeClosureParams [] (xs' ++ ks'), e')
  env <- makeClosureEnv flds
  let fnName (K.TmVar x i) = Name x i
  pure (FunClosureDef (fnName f) env params' e')
cconvFunDef (K.AbsDef _ f as ks e) = do
  ((params', e'), flds) <- listen $
    withTys as $ \as' -> do
      withCos ks $ \ks' -> do
        e' <- cconv e
        pure (makeClosureParams as' ks', e')
  env <- makeClosureEnv flds
  let fnName (K.TmVar x i) = Name x i
  pure (FunClosureDef (fnName f) env params' e')

cconvContDef :: K.ContDef a -> ConvM (Name, ContClosureDef)
cconvContDef (K.ContDef _ k xs e) = do
  ((xs', e'), flds) <- listen $
    withTms xs $ \xs' -> do
      e' <- cconv e
      pure (xs', e')
  env <- makeClosureEnv flds
  let contName (K.CoVar x i) = Name x i
  pure (contName k, ContClosureDef env xs' e')

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
    ftv ctx (Sum t1 t2) = ftv ctx t1 <> ftv ctx t2
    ftv ctx (Pair t1 t2) = ftv ctx t1 <> ftv ctx t2
    ftv ctx (List t) = ftv ctx t


cconvValue :: K.ValueK -> ConvM ValueC
cconvValue K.NilK = pure NilC
cconvValue (K.PairK x y) = PairC <$> cconvTmVar x <*> cconvTmVar y
cconvValue (K.IntValK i) = pure (IntC i)
cconvValue (K.BoolValK b) = pure (BoolC b)
cconvValue (K.InlK x) = InlC <$> cconvTmVar x
cconvValue (K.InrK y) = InrC <$> cconvTmVar y
cconvValue K.EmptyK = pure EmptyC
cconvValue (K.ConsK x y) = ConsC <$> cconvTmVar x <*> cconvTmVar y
cconvValue (K.StringValK s) = pure (StringC s)
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

cconvTyVar :: K.TyVar -> ConvM TyVar
cconvTyVar aa = do
  tys <- asks ctxTys
  case Map.lookup aa tys of
    Nothing -> error ("type variable not in scope: " ++ show aa)
    Just (aa', k) -> writer (aa', singleTyOcc aa' k)



