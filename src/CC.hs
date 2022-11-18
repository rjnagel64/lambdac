
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
  , ctxTys :: Map K.TyVar TyVar
  }

emptyContext :: Context
emptyContext = Context Map.empty Map.empty Map.empty

data FreeOcc = FreeOcc { freeOccName :: Name, freeOccSort :: Sort }

instance Eq FreeOcc where
  (==) = (==) `on` freeOccName

instance Ord FreeOcc where
  compare = compare `on` freeOccName

newtype Fields = Fields { getFields :: (Set FreeOcc, Set TyVar) }

instance Semigroup Fields where
  f <> g = Fields $ getFields f <> getFields g

instance Monoid Fields where
  mempty = Fields (Set.empty, Set.empty)

singleOcc :: Name -> Sort -> Fields
singleOcc x s = Fields (Set.singleton (FreeOcc x s), ftv s)
  where
    ftv :: Sort -> Set TyVar
    ftv (Alloc aa) = Set.singleton aa
    ftv (Closure tele) = foldr f Set.empty tele
      where
        f (ValueTele t) acc = ftv t <> acc
        f (TypeTele aa) acc = Set.delete aa acc
    ftv Integer = Set.empty
    ftv Unit = Set.empty
    ftv Sum = Set.empty
    ftv Boolean = Set.empty
    ftv String = Set.empty
    ftv (Pair t1 t2) = ftv t1 <> ftv t2
    ftv (List t) = ftv t

bindOccs :: Foldable t => t (Name, Sort) -> Fields -> Fields
bindOccs bs flds =
  let bs' = Set.fromList $ map (\ (x, s) -> FreeOcc x s) $ toList bs in
  let (occs, tys) = getFields flds in
  Fields (occs Set.\\ bs', tys)

singleTyOcc :: TyVar -> Fields
singleTyOcc aa = Fields (Set.empty, Set.singleton aa)

bindTys :: [TyVar] -> Fields -> Fields
bindTys aas flds =
  let (occs, tys) = getFields flds in
  Fields (occs, tys Set.\\ Set.fromList aas)

newtype ConvM a = ConvM { runConvM :: ReaderT Context (Writer Fields) a }

deriving instance Functor ConvM
deriving instance Applicative ConvM
deriving instance Monad ConvM

deriving instance MonadReader Context ConvM
deriving instance MonadWriter Fields ConvM

runConv :: ConvM a -> a
runConv = fst . runWriter . flip runReaderT emptyContext . runConvM

insertMany :: Ord k => [(k, v)] -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

-- | Bind a sequence of term variables: both extending the typing context on
-- the way down, and removing them from the free variable set on the way back
-- up.
withTms :: Traversable t => t (K.TmVar, K.TypeK) -> (t (Name, Sort) -> ConvM a) -> ConvM a
withTms xs k = do
  xs' <- traverse (\ (x, t) -> sortOf t >>= \t' -> pure (x, (tmVar x, t'))) xs
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
  ks' <- traverse (\ (x, t) -> coSortOf t >>= \t' -> pure (x, (coVar x, t'))) ks
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
withTys :: [K.TyVar] -> ([TyVar] -> ConvM a) -> ConvM a
withTys aas k = do
  let aas' = map (\aa -> (aa, tyVar aa)) aas
  let extend (Context tms cos tys) = Context tms cos (insertMany aas' tys)
  let binds = map snd aas'
  censor (bindTys binds) $ local extend $ k binds
  where
    -- Hmm. I'm pretty sure I don't have to worry about shadowing, but I should
    -- double-check that.
    tyVar :: K.TyVar -> TyVar
    tyVar (K.TyVar aa i) = TyVar (aa ++ show i)

-- | A special case of 'withTms', for binding a single term variable.
withTm :: (K.TmVar, K.TypeK) -> ((Name, Sort) -> ConvM a) -> ConvM a
withTm b k = withTms (Identity b) (k . runIdentity)


cconvProgram :: K.TermK a -> TermC
cconvProgram e = runConv (cconv e)

cconv :: K.TermK a -> ConvM TermC
cconv (K.HaltK x) = HaltC <$> cconvTmVar x
cconv (K.JumpK k xs) = JumpC <$> cconvCoVar k <*> traverse cconvTmVar xs
cconv (K.CallK f xs ks) = CallC <$> cconvTmVar f <*> traverse cconvTmVar xs <*> traverse cconvCoVar ks
cconv (K.InstK f ts ks) = InstC <$> cconvTmVar f <*> traverse sortOf ts <*> traverse cconvCoVar ks 
cconv (K.CaseK x t ks) = CaseC <$> cconvTmVar x <*> caseKind t <*> traverse cconvCoVar ks
cconv (K.LetFstK x t y e) = withTm (x, t) $ \b -> LetFstC b <$> cconvTmVar y <*> cconv e
cconv (K.LetSndK x t y e) = withTm (x, t) $ \b -> LetSndC b <$> cconvTmVar y <*> cconv e
cconv (K.LetValK x t v e) = withTm (x, t) $ \b -> LetValC b <$> cconvValue v <*> cconv e
cconv (K.LetArithK x op e) = withTm (x, K.IntK) $ \b -> LetArithC b <$> cconvArith op <*> cconv e
cconv (K.LetNegateK x y e) = withTm (x, K.IntK) $ \b -> LetNegateC b <$> cconvTmVar y <*> cconv e
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
  let (fields, tyfields) = getFields flds
  let env = EnvDef (Set.toList tyfields) (map (\ (FreeOcc x s) -> (x, s)) $ Set.toList fields)
  let fnName (K.TmVar x i) = Name x i
  pure (FunClosureDef (fnName f) env params' e')
cconvFunDef (K.AbsDef _ f as ks e) = do
  ((params', e'), flds) <- listen $
    withTys as $ \as' -> do
      withCos ks $ \ks' -> do
        e' <- cconv e
        pure (makeClosureParams as' ks', e')
  let (fields, tyfields) = getFields flds
  let env = EnvDef (Set.toList tyfields) (map (\ (FreeOcc x s) -> (x, s)) $ Set.toList fields)
  let fnName (K.TmVar x i) = Name x i
  pure (FunClosureDef (fnName f) env params' e')

cconvContDef :: K.ContDef a -> ConvM ContClosureDef
cconvContDef (K.ContDef _ k xs e) = do
  ((xs', e'), flds) <- listen $
    withTms xs $ \xs' -> do
      e' <- cconv e
      pure (xs', e')
  let (fields, tyfields) = getFields flds
  let env = EnvDef (Set.toList tyfields) (map (\ (FreeOcc x s) -> (x, s)) $ Set.toList fields)
  let contName (K.CoVar x i) = Name x i
  pure (ContClosureDef (contName k) env xs' e')

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

cconvArith :: K.ArithK -> ConvM ArithC
cconvArith (K.AddK x y) = AddC <$> cconvTmVar x <*> cconvTmVar y
cconvArith (K.SubK x y) = SubC <$> cconvTmVar x <*> cconvTmVar y
cconvArith (K.MulK x y) = MulC <$> cconvTmVar x <*> cconvTmVar y

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
    Just aa' -> writer (aa', singleTyOcc aa')


sortOf :: K.TypeK -> ConvM Sort
sortOf (K.TyVarOccK aa) = Alloc <$> cconvTyVar aa
sortOf (K.AllK aas ss) = do
  withTys aas $ \aas' -> do
    ss' <- traverse coSortOf ss
    let tele = map TypeTele aas' ++ map ValueTele ss'
    pure (Closure tele)
sortOf K.UnitK = pure Unit
sortOf K.IntK = pure Integer
sortOf K.BoolK = pure Boolean
sortOf K.StringK = pure String
sortOf (K.SumK _ _) = pure Sum
sortOf (K.ListK t) = List <$> sortOf t
sortOf (K.ProdK t1 t2) = Pair <$> sortOf t1 <*> sortOf t2
sortOf (K.FunK ts ss) = f <$> traverse sortOf ts <*> traverse coSortOf ss
  where f ts' ss' = Closure (map ValueTele ts' ++ map ValueTele ss')

coSortOf :: K.CoTypeK -> ConvM Sort
coSortOf (K.ContK ss) = do
  ss' <- traverse sortOf ss
  let tele = map ValueTele ss'
  pure (Closure tele)

caseKind :: K.TypeK -> ConvM CaseKind
caseKind K.BoolK = pure CaseBool
caseKind (K.SumK a b) = CaseSum <$> sortOf a <*> sortOf b
caseKind (K.ListK a) = CaseList <$> sortOf a
caseKind _ = error "cannot perform case analysis on this type"


