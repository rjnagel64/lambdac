{-# LANGUAGE
    DerivingStrategies
  , GeneralizedNewtypeDeriving
  , StandaloneDeriving
  , FlexibleInstances
  , MultiParamTypeClasses
  #-}

module CC
  ( TermC(..)
  , CaseKind(..)
  , FunClosureDef(..)
  , funClosureSort
  , ContClosureDef(..)
  , contClosureSort
  , AbsClosureDef(..)
  , absClosureSort
  , EnvDef(..)
  , Name(..)
  , prime
  , ValueC(..)
  , ArithC(..)
  , CmpC(..)
  , BranchType(..)
  , Sort(..)
  , TeleEntry(..)
  , TyVar(..)

  , cconv
  , runConv
  , pprintTerm
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)

import Data.Function (on)
import Data.List (intercalate)
import Data.Bifunctor
import Prelude hiding (abs, cos)

import qualified CPS as K
import CPS (TermK(..), FunDef(..), ContDef(..), AbsDef(..), ValueK(..), ArithK(..), CmpK(..))

-- Closure conversion:
-- https://gist.github.com/jozefg/652f1d7407b7f0266ae9
--
-- Example:
-- let a = 4; b = 3; in let f = \x -> \y -> a*x + b*y in f 2 5
-- let a = 4; b = 3; in
--   let
--     f = <{a := a, b := b}, \x -> <{a := a, b := b, x = x}, \y -> a*x + b*y>>;
--   in
--     f 2 5

-- Note: [Closure Conversion and Lifting]
-- After closure conversion, every lambda is annotated with its free variables.
-- If there are no free variables, the lambda can be trivially lifted to the top level.
-- If there are free variables, [Selective Lambda Lifting.pdf] can optionally
-- lift if it would be beneficial.
-- However, not all closures can/should be lifted. For example, consider a
-- lambda in a loop, that captures a different value of 'n' each time.
--
-- For compilation, there is still some "hoisting" that needs to be done,
-- because the code pointer for each lambda needs to be defined at the top
-- level, and also because the struct for the captured variables needs to be
-- hoisted too.

-- cconvTy :: TypeK -> TypeC
-- cconvTy (a -> b) = ∃c. (c -> cconvTy a -> cconvTy b) × c
-- (actually, CPS types rather than a -> b, but approximately.)
-- (Also, this version tends to have lots of fst/snd from nested pairs. Could
-- do n-ary tuples instead.)

-- The sort of a name can be determined from where it is bound.
data Name = Name String Int
  deriving (Eq, Ord)

instance Show Name where
  show (Name x i) = x ++ show i

prime :: Name -> Name
prime (Name x i) = Name x (i+1)

-- TODO: Eliminate tmVar, coVar, and tyVar. They are not aware of the Context.
tmVar :: K.TmVar -> Name
tmVar (K.TmVar x i) = Name x i

coVar :: K.CoVar -> Name
coVar (K.CoVar k i) = Name k i

data TyVar = TyVar String
  deriving (Eq, Ord)

instance Show TyVar where
  show (TyVar aa) = aa

tyVar :: K.TyVar -> TyVar
tyVar (K.TyVar aa i) = TyVar (aa ++ show i)

-- | 'Sort' is really a simplified form of type information.
-- Value = int
-- Sum = bool | t1 + t2
-- Product = () | t1 * t2
-- Closure = (t1, t2, ...) -> 0
-- Alloc = a : *
-- Eventually, I may want to distinguish between named and anonymous product
-- types.
data Sort
  = Closure [TeleEntry]
  | Integer
  | Alloc TyVar
  | Sum
  | Pair Sort Sort
  | Unit
  | Boolean
  | List Sort

instance Show Sort where
  show (Closure ss) = "(" ++ intercalate ", " (map show ss) ++ ") -> !"
  show Integer = "int"
  show (Alloc aa) = "alloc(" ++ show aa ++ ")"
  show Sum = "sum"
  show Boolean = "bool"
  show (List s) = "list " ++ show s
  show (Pair s t) = "pair " ++ show s ++ " " ++ show t
  show Unit = "unit"

data TeleEntry
  = ValueTele Sort
  | TypeTele TyVar

instance Show TeleEntry where
  show (ValueTele s) = show s
  show (TypeTele aa) = '@' : show aa

sortOf :: K.TypeK -> Sort
sortOf (K.SumK _ _) = Sum
sortOf K.BoolK = Boolean
sortOf (K.ProdK t1 t2) = Pair (sortOf t1) (sortOf t2)
sortOf K.UnitK = Unit
sortOf K.IntK = Integer
sortOf (K.ListK t) = List (sortOf t)
sortOf (K.FunK ts ss) = Closure (map (ValueTele . sortOf) ts ++ map (ValueTele . coSortOf) ss)
sortOf (K.TyVarOccK aa) = Alloc (tyVar aa)
sortOf (K.AllK aas ss) = Closure (map (TypeTele . tyVar) aas ++ map (ValueTele . coSortOf) ss)

coSortOf :: K.CoTypeK -> Sort
coSortOf (K.ContK ss) = Closure (map (ValueTele . sortOf) ss)

-- Closure conversion is bottom-up (to get flat closures) traversal that
-- replaces free variables with references to an environment parameter.
data TermC
  = LetValC (Name, Sort) ValueC TermC -- let x = v in e, allocation
  | LetFstC (Name, Sort) Name TermC -- let x = fst y in e, projection
  | LetSndC (Name, Sort) Name TermC
  | LetArithC (Name, Sort) ArithC TermC
  | LetNegateC (Name, Sort) Name TermC -- let x = -y in e, unary negation
  | LetCompareC (Name, Sort) CmpC TermC
  | LetFunC [FunClosureDef] TermC
  | LetContC [ContClosureDef] TermC
  | LetAbsC [AbsClosureDef] TermC
  -- Invoke a closure by providing values for the remaining arguments.
  | JumpC Name [Name] -- k x...
  | CallC Name [Name] [Name] -- f x+ k+
  | HaltC Name
  | CaseC Name CaseKind [Name] -- case x of k1 | k2 | ...
  | InstC Name [Sort] [Name] -- f @t+ k+

data CaseKind
  = CaseBool
  | CaseSum Sort Sort
  | CaseList Sort

caseKind :: K.TypeK -> CaseKind
caseKind K.BoolK = CaseBool
caseKind (K.SumK a b) = CaseSum (sortOf a) (sortOf b)
caseKind (K.ListK a) = CaseList (sortOf a)
caseKind _ = error "cannot perform case analysis on this type"

-- | A 'BranchType' specifies the argument sorts expected by a case branch.
newtype BranchType = BranchType [Sort]

data ArithC
  = AddC Name Name
  | SubC Name Name
  | MulC Name Name

data CmpC
  = EqC Name Name
  | NeC Name Name
  | LtC Name Name
  | LeC Name Name
  | GtC Name Name
  | GeC Name Name

-- | @f {x+} y+ k+ = e@
-- Closures capture two sets of names: those from outer scopes, and those from
-- the same recursive bind group.
data FunClosureDef
  = FunClosureDef {
    funClosureName :: Name
  , funEnvDef :: EnvDef
  , funClosureParams :: [(Name, Sort)]
  , funClosureConts :: [(Name, Sort)]
  , funClosureBody :: TermC
  }

funClosureSort :: FunClosureDef -> Sort
funClosureSort (FunClosureDef _ _ params conts _) =
  Closure (map (ValueTele . snd) params ++ map (ValueTele . snd) conts)

data ContClosureDef
  = ContClosureDef {
    contClosureName :: Name
  , contEnvDef :: EnvDef
  , contClosureParams :: [(Name, Sort)]
  , contClosureBody :: TermC
  }

contClosureSort :: ContClosureDef -> Sort
contClosureSort (ContClosureDef _ _ params _) = Closure (map (ValueTele . snd) params)

data AbsClosureDef
  = AbsClosureDef {
    absClosureName :: Name
  , absEnvDef :: EnvDef
  , absClosureTypes :: [TyVar]
  , absClosureConts :: [(Name, Sort)]
  , absClosureBody :: TermC
  }

absClosureSort :: AbsClosureDef -> Sort
absClosureSort (AbsClosureDef _ _ types conts _) = Closure (map TypeTele types ++ map (ValueTele . snd) conts)

-- | Closures environments capture two sets of names: those from outer scopes,
-- and those from the same recursive bind group.
data EnvDef
  = EnvDef {
    envFreeTypes :: [TyVar]
  , envFreeNames :: [(Name, Sort)]
  }

data ValueC
  = PairC Name Name
  | NilC
  | InlC Name
  | InrC Name
  | IntC Int
  | BoolC Bool
  | EmptyC
  | ConsC Name Name


data FreeOcc = FreeOcc { freeOccName :: Name, freeOccSort :: Sort }

freeOcc :: FreeOcc -> (Name, Sort)
freeOcc (FreeOcc x s) = (x, s)

instance Eq FreeOcc where
  (==) = (==) `on` freeOccName

instance Ord FreeOcc where
  compare = compare `on` freeOccName

-- I'm not entirely satisfied with the existence of 'FieldsFor'. It should be a
-- bottom-up traversal, just like the 'cconv' pass, but I end up separating it
-- out and repeatedly invoking it. (the time complexity is not correct.)
--
-- I think that the "proper" way to do it is with a Writer monad, and using
-- 'censor' to implement 'bindFields'? I might just keep it as part of the
-- return value, though.
newtype FieldsFor = FieldsFor { runFieldsFor :: Context -> (Set FreeOcc, Set TyVar) }

data Context
  = Context {
    ctxTms :: Map K.TmVar (Name, Sort)
  , ctxCos :: Map K.CoVar (Name, Sort)
  , ctxTys :: Map K.TyVar TyVar
  }

instance Semigroup FieldsFor where
  fs <> fs' = FieldsFor $ \ctx -> runFieldsFor fs ctx <> runFieldsFor fs' ctx

instance Monoid FieldsFor where
  mempty = FieldsFor $ \_ -> (Set.empty, Set.empty)

unitTm :: K.TmVar -> FieldsFor
unitTm x = FieldsFor $ \ctx -> case Map.lookup x (ctxTms ctx) of
  Nothing -> error ("unbound variable occurrence: " ++ show x ++ " not in " ++ show (ctxTms ctx))
  Just (x', s) -> (Set.singleton (FreeOcc x' s), Set.empty)

unitCo :: K.CoVar -> FieldsFor
unitCo k = FieldsFor $ \ctx -> case Map.lookup k (ctxCos ctx) of
  Nothing -> error ("unbound variable occurrence: " ++ show k ++ " not in " ++ show (ctxCos ctx))
  Just (k', s) -> (Set.singleton (FreeOcc k' s), Set.empty)

unitTy :: K.TyVar -> FieldsFor
unitTy aa = FieldsFor $ \ctx -> case Map.lookup aa (ctxTys ctx) of
  Nothing -> error ("unbound type variable occurrence: " ++ show aa ++ " not in " ++ show (ctxTys ctx))
  Just aa' -> (Set.empty, Set.singleton aa')


insertMany :: Ord k => [(k, v)] -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

bindTms :: [(K.TmVar, K.TypeK)] -> FieldsFor -> FieldsFor
bindTms xs f = FieldsFor $ \ctx ->
  let xs' = map (\b -> (fst b, bimap tmVar sortOf b)) xs in
  let ctx' = ctx { ctxTms = insertMany xs' (ctxTms ctx) } in
  let (fields, tyfields) = runFieldsFor f ctx' in
  let bound = Set.fromList $ map (\ (_, (x, s)) -> FreeOcc x s) xs' in
  (fields Set.\\ bound, tyfields)

bindCos :: [(K.CoVar, K.CoTypeK)] -> FieldsFor -> FieldsFor
bindCos ks f = FieldsFor $ \ctx ->
  let ks' = map (\b -> (fst b, bimap coVar coSortOf b)) ks in
  let ctx' = ctx { ctxCos = insertMany ks' (ctxCos ctx) } in
  let (fields, tyfields) = runFieldsFor f ctx' in
  let bound = Set.fromList $ map (\ (_, (k, s)) -> FreeOcc k s) ks' in
  (fields Set.\\ bound, tyfields)

bindTys :: [K.TyVar] -> FieldsFor -> FieldsFor
bindTys aas f = FieldsFor $ \ctx ->
  let aas' = map (\a -> (a, tyVar a)) aas in
  let ctx' = ctx { ctxTys = insertMany aas' (ctxTys ctx) } in
  let (fields, tyfields) = runFieldsFor f ctx' in
  let bound = Set.fromList (map snd aas') in
  (fields, tyfields Set.\\ bound)


fieldsFor :: TermK a -> FieldsFor
fieldsFor (LetFunK fs e) =
  bindTms fs' $ foldMap (fieldsForFunDef) fs <> fieldsFor e
  where fs' = [(f, K.FunK (map snd xs) (map snd ks)) | FunDef _ f xs ks _ <- fs]
fieldsFor (LetContK ks e) =
  bindCos ks' $ foldMap (fieldsForContDef) ks <> fieldsFor e
  where ks' = [(k, K.ContK (map snd xs)) | ContDef _ k xs _ <- ks]
fieldsFor (LetAbsK fs e) =
  bindTms fs' $ foldMap (fieldsForAbsDef) fs <> fieldsFor e
  where fs' = [(f, K.AllK as (map snd ks)) | AbsDef _ f as ks _ <- fs]
fieldsFor (HaltK x) = unitTm x
fieldsFor (JumpK k xs) = unitCo k <> foldMap unitTm xs
fieldsFor (CallK f xs ks) = unitTm f <> foldMap unitTm xs <> foldMap unitCo ks
fieldsFor (CaseK x _ ks) = unitTm x <> foldMap unitCo ks
fieldsFor (InstK f ts ks) = unitTm f <> foldMap fieldsForTy ts <> foldMap unitCo ks
fieldsFor (LetFstK x t y e) =
  unitTm y <> fieldsForTy t <> bindTms [(x, t)] (fieldsFor e)
fieldsFor (LetSndK x t y e) =
  unitTm y <> fieldsForTy t <> bindTms [(x, t)] (fieldsFor e)
fieldsFor (LetValK x t v e) =
  fieldsForValue v <> fieldsForTy t <> bindTms [(x, t)] (fieldsFor e)
fieldsFor (LetArithK x op e) = fieldsForArith op <> bindTms [(x, K.IntK)] (fieldsFor e)
fieldsFor (LetNegateK x y e) = unitTm y <> bindTms [(x, K.IntK)] (fieldsFor e)
fieldsFor (LetCompareK x cmp e) = fieldsForCmp cmp <> bindTms [(x, K.BoolK)] (fieldsFor e)

fieldsForArith :: ArithK -> FieldsFor
fieldsForArith (AddK x y) = unitTm x <> unitTm y
fieldsForArith (SubK x y) = unitTm x <> unitTm y
fieldsForArith (MulK x y) = unitTm x <> unitTm y

fieldsForCmp :: CmpK -> FieldsFor
fieldsForCmp (CmpEqK x y) = unitTm x <> unitTm y
fieldsForCmp (CmpNeK x y) = unitTm x <> unitTm y
fieldsForCmp (CmpLtK x y) = unitTm x <> unitTm y
fieldsForCmp (CmpLeK x y) = unitTm x <> unitTm y
fieldsForCmp (CmpGtK x y) = unitTm x <> unitTm y
fieldsForCmp (CmpGeK x y) = unitTm x <> unitTm y

fieldsForValue :: ValueK -> FieldsFor
fieldsForValue (IntValK _) = mempty
fieldsForValue (BoolValK _) = mempty
fieldsForValue NilK = mempty
fieldsForValue (PairK x y) = unitTm x <> unitTm y
fieldsForValue (InlK x) = unitTm x
fieldsForValue (InrK y) = unitTm y
fieldsForValue EmptyK = mempty
fieldsForValue (ConsK x y) = unitTm x <> unitTm y

fieldsForFunDef :: FunDef a -> FieldsFor
fieldsForFunDef (FunDef _ _f xs ks e) =
  bindTms xs (bindCos ks (fieldsFor e)) <>
  foldMap (fieldsForTy . snd) xs <>
  foldMap (fieldsForCoTy . snd) ks

fieldsForContDef :: ContDef a -> FieldsFor
fieldsForContDef (ContDef _ _k xs e) =
  bindTms xs (fieldsFor e) <>
  foldMap (fieldsForTy . snd) xs

fieldsForAbsDef :: AbsDef a -> FieldsFor
fieldsForAbsDef (AbsDef _ _f as ks e) =
  bindTys as $
    foldMap (fieldsForCoTy . snd) ks <>
    bindCos ks (fieldsFor e)

fieldsForTy :: K.TypeK -> FieldsFor
fieldsForTy K.UnitK = mempty
fieldsForTy K.IntK = mempty
fieldsForTy K.BoolK = mempty
fieldsForTy (K.ProdK t s) = fieldsForTy t <> fieldsForTy s
fieldsForTy (K.SumK t s) = fieldsForTy t <> fieldsForTy s
fieldsForTy (K.ListK t) = fieldsForTy t
fieldsForTy (K.FunK ts ss) = foldMap fieldsForTy ts <> foldMap fieldsForCoTy ss
fieldsForTy (K.TyVarOccK aa) = unitTy aa
fieldsForTy (K.AllK aas ss) = bindTys aas (foldMap fieldsForCoTy ss)

fieldsForCoTy :: K.CoTypeK -> FieldsFor
fieldsForCoTy (K.ContK ss) = foldMap fieldsForTy ss

-- | Compute the free type variables of a 'Sort'.
-- Kind of a hack; used to make sure that environments contain all the type
-- variables needed by their value fields.
ftv :: Sort -> Set TyVar
ftv (Alloc aa) = Set.singleton aa
ftv (Closure tele) = foldr f Set.empty tele
  where
    f (ValueTele s) acc = ftv s <> acc
    f (TypeTele aa) acc = Set.delete aa acc
ftv Integer = Set.empty
ftv Unit = Set.empty
ftv Sum = Set.empty
ftv Boolean = Set.empty
ftv (Pair t s) = ftv t <> ftv s
ftv (List s) = ftv s

-- TODO: The typing context for ConvM should be
-- '(Map K.TmVar (Name, Sort), Map K.CoVar (Name, Sort), Map K.TyVar TyVar)'
newtype ConvM a = ConvM { runConvM :: Reader Context a }

deriving newtype instance Functor ConvM
deriving newtype instance Applicative ConvM
deriving newtype instance Monad ConvM
deriving newtype instance MonadReader Context ConvM

runConv :: ConvM a -> a
runConv = flip runReader emptyContext . runConvM
  where emptyContext = Context Map.empty Map.empty Map.empty

withTm :: K.TmVar -> K.TypeK -> ((Name, Sort) -> ConvM a) -> ConvM a
withTm x t kont = local extend (kont (x', t'))
  where
    x' = tmVar x
    t' = sortOf t
    extend (Context tms cos tys) = Context (Map.insert x (x', t') tms) cos tys

withTmBinds :: [(K.TmVar, K.TypeK)] -> ([(Name, Sort)] -> ConvM a) -> ConvM a
withTmBinds xs kont = local extend (kont (map snd tmbinds))
  where
    tmbinds = map (\ (x, t) -> (x, (tmVar x, sortOf t))) xs
    extend (Context tms cos tys) = Context (insertMany tmbinds tms) cos tys

withCoBinds :: [(K.CoVar, K.CoTypeK)] -> ([(Name, Sort)] -> ConvM a) -> ConvM a
withCoBinds ks kont = local extend (kont (map snd cobinds))
  where
    cobinds = map (\ (k, s) -> (k, (coVar k, coSortOf s))) ks
    extend (Context tms cos tys) = Context tms (insertMany cobinds cos) tys

withTyBinds :: [K.TyVar] -> ([TyVar] -> ConvM a) -> ConvM a
withTyBinds as kont = local extend (kont (map snd tybinds))
  where
    tybinds = map (\a -> (a, tyVar a)) as
    extend (Context tms cos tys) = Context tms cos (insertMany tybinds tys)


-- Idea: I could factor out the fieldsFor computation by doing a first
-- annotation pass over the data, and then having
-- 'cconv :: TermK EnvFields -> ConvM TermC'
-- This does get a bit messy with both TmVar/CoVar and Name being present,
-- though.
cconv :: TermK a -> ConvM TermC
cconv (LetFunK fs e) = do
  let tmbinds = [(f, K.FunK (map snd xs) (map snd ks)) | FunDef _ f xs ks _ <- fs]
  withTmBinds tmbinds $ \tmbinds' -> LetFunC <$> traverse cconvFunDef fs <*> cconv e
cconv (LetContK ks e) = do
  let cobinds = [(k, K.ContK (map snd xs)) | ContDef _ k xs _ <- ks]
  withCoBinds cobinds $ \cobinds' -> LetContC <$> traverse cconvContDef ks <*> cconv e
cconv (LetAbsK fs e) = do
  let tmbinds = [(f, K.AllK as (map snd ks)) | AbsDef _ f as ks _ <- fs]
  withTmBinds tmbinds $ \tmbinds' -> LetAbsC <$> traverse cconvAbsDef fs <*> cconv e
cconv (HaltK x) = HaltC <$> cconvTmVar x
cconv (JumpK k xs) = JumpC <$> cconvCoVar k <*> traverse cconvTmVar xs
cconv (CallK f xs ks) = CallC <$> cconvTmVar f <*> traverse cconvTmVar xs <*> traverse cconvCoVar ks
cconv (InstK f ts ks) = InstC <$> cconvTmVar f <*> pure (map sortOf ts) <*> traverse cconvCoVar ks
cconv (CaseK x t ks) = CaseC <$> cconvTmVar x <*> pure (caseKind t) <*> traverse cconvCoVar ks
cconv (LetFstK x t y e) = withTm x t $ \b -> LetFstC b <$> cconvTmVar y <*> cconv e
cconv (LetSndK x t y e) = withTm x t $ \b -> LetSndC b <$> cconvTmVar y <*> cconv e
cconv (LetValK x t v e) = withTm x t $ \b -> LetValC b <$> cconvValue v <*> cconv e
cconv (LetArithK x op e) = withTm x K.IntK $ \b -> LetArithC b <$> cconvArith op <*> cconv e
cconv (LetNegateK x y e) = withTm x K.IntK $ \b -> LetNegateC b <$> cconvTmVar y <*> cconv e
cconv (LetCompareK x cmp e) = withTm x K.BoolK $ \b -> LetCompareC b <$> cconvCmp cmp <*> cconv e

cconvFunDef :: FunDef a -> ConvM FunClosureDef
cconvFunDef fun@(FunDef _ f xs ks e) = do
  withTmBinds xs $ \tmbinds -> do
    withCoBinds ks $ \cobinds -> do
      env <- cconvEnvDef fieldsForFunDef fun
      e' <- cconv e
      pure (FunClosureDef (tmVar f) env tmbinds cobinds e')

cconvContDef :: ContDef a -> ConvM ContClosureDef
cconvContDef kont@(ContDef _ k xs e) = do
  withTmBinds xs $ \tmbinds -> do
    env <- cconvEnvDef fieldsForContDef kont
    e' <- cconv e
    pure (ContClosureDef (coVar k) env tmbinds e')

cconvAbsDef :: AbsDef a -> ConvM AbsClosureDef
cconvAbsDef abs@(AbsDef _ f as ks e) = do
  withTyBinds as $ \tybinds -> do
    withCoBinds ks $ \cobinds -> do
      env <- cconvEnvDef fieldsForAbsDef abs
      e' <- cconv e
      pure (AbsClosureDef (tmVar f) env tybinds cobinds e')

cconvEnvDef :: (a -> FieldsFor) -> a -> ConvM EnvDef
cconvEnvDef fieldsForDef def = do
  ctx <- ask
  let (fields, tyfields) = runFieldsFor (fieldsForDef def) ctx
  let tyfields' = foldr (\occ tys -> ftv (freeOccSort occ) <> tys) tyfields (Set.toList fields)
  let env = EnvDef (Set.toList tyfields') (map freeOcc $ Set.toList fields)
  pure env

cconvTmVar :: K.TmVar -> ConvM Name
cconvTmVar x = do
  tms <- asks ctxTms
  case Map.lookup x tms of
    Nothing -> error ("variable not in scope: " ++ show x)
    Just (x', _) -> pure x'

cconvCoVar :: K.CoVar -> ConvM Name
cconvCoVar k = do
  cos <- asks ctxCos
  case Map.lookup k cos of
    Nothing -> error ("variable not in scope: " ++ show k)
    Just (k', _) -> pure k'

cconvValue :: ValueK -> ConvM ValueC
cconvValue NilK = pure NilC
cconvValue (PairK x y) = PairC <$> cconvTmVar x <*> cconvTmVar y
cconvValue (IntValK i) = pure (IntC i)
cconvValue (BoolValK b) = pure (BoolC b)
cconvValue (InlK x) = InlC <$> cconvTmVar x
cconvValue (InrK y) = InrC <$> cconvTmVar y
cconvValue EmptyK = pure EmptyC
cconvValue (ConsK x y) = ConsC <$> cconvTmVar x <*> cconvTmVar y

cconvArith :: ArithK -> ConvM ArithC
cconvArith (AddK x y) = AddC <$> cconvTmVar x <*> cconvTmVar y
cconvArith (SubK x y) = SubC <$> cconvTmVar x <*> cconvTmVar y
cconvArith (MulK x y) = MulC <$> cconvTmVar x <*> cconvTmVar y

cconvCmp :: CmpK -> ConvM CmpC
cconvCmp (CmpEqK x y) = EqC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (CmpNeK x y) = NeC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (CmpLtK x y) = LtC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (CmpLeK x y) = LeC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (CmpGtK x y) = GtC <$> cconvTmVar x <*> cconvTmVar y
cconvCmp (CmpGeK x y) = GeC <$> cconvTmVar x <*> cconvTmVar y

-- What does well-typed closure conversion look like?
-- How are the values in a closure bound?

-- Closure conversion is not lambda lifting.
-- CC involves capturing the environment when a function is created (but the
-- call site remains mostly the same), LL requires altering the call sites.
-- (LL is O(n^3) or O(n^2), CC is less?)
-- https://pages.github.ccs.neu.edu/jhemann/21SP-CS4400/FAQ/closure-conv/


indent :: Int -> String -> String
indent n s = replicate n ' ' ++ s

pprintTerm :: Int -> TermC -> String
pprintTerm n (HaltC x) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (JumpC k xs) = indent n $ show k ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CallC f xs ks) =
  indent n $ show f ++ " " ++ intercalate " " (map show xs ++ map show ks) ++ ";\n"
pprintTerm n (InstC f ss ks) =
  indent n $ intercalate " @" (show f : map show ss) ++ " " ++ intercalate " " (map show ks) ++ ";\n"
pprintTerm n (LetFunC fs e) =
  indent n "letfun\n" ++ concatMap (pprintFunClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContC fs e) =
  indent n "letcont\n" ++ concatMap (pprintContClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetAbsC fs e) =
  indent n "letabs\n" ++ concatMap (pprintAbsClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e 
pprintTerm n (LetValC x v e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintValue v ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetFstC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = fst " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetSndC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = snd " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (CaseC x _ ks) =
  let branches = intercalate " | " (map show ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetArithC x op e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetNegateC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = -" ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetCompareC x cmp e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintCompare cmp ++ ";\n") ++ pprintTerm n e

pprintPlace :: (Name, Sort) -> String
pprintPlace (x, s) = show x ++ " : " ++ show s

pprintValue :: ValueC -> String
pprintValue NilC = "()"
pprintValue (PairC x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntC i) = show i
pprintValue (BoolC b) = if b then "true" else "false"
pprintValue (InlC x) = "inl " ++ show x
pprintValue (InrC y) = "inr " ++ show y
pprintValue EmptyC = "nil"
pprintValue (ConsC x xs) = "cons " ++ show x ++ " " ++ show xs

pprintArith :: ArithC -> String
pprintArith (AddC x y) = show x ++ " + " ++ show y
pprintArith (SubC x y) = show x ++ " - " ++ show y
pprintArith (MulC x y) = show x ++ " * " ++ show y

pprintCompare :: CmpC -> String
pprintCompare (EqC x y) = show x ++ " == " ++ show y
pprintCompare (NeC x y) = show x ++ " != " ++ show y
pprintCompare (LtC x y) = show x ++ " < " ++ show y
pprintCompare (LeC x y) = show x ++ " <= " ++ show y
pprintCompare (GtC x y) = show x ++ " > " ++ show y
pprintCompare (GeC x y) = show x ++ " >= " ++ show y

pprintFunClosureDef :: Int -> FunClosureDef -> String
pprintFunClosureDef n (FunClosureDef f env xs ks e) =
  pprintEnvDef n env ++ indent n (show f ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    params = "(" ++ intercalate ", " args ++ ")"
    args = map pprintPlace xs ++ map pprintPlace ks

pprintContClosureDef :: Int -> ContClosureDef -> String
pprintContClosureDef n (ContClosureDef k env xs e) =
  pprintEnvDef n env ++ indent n (show k ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    params = "(" ++ intercalate ", " args ++ ")"
    args = map pprintPlace xs

pprintAbsClosureDef :: Int -> AbsClosureDef -> String
pprintAbsClosureDef n (AbsClosureDef f env as ks e) =
  pprintEnvDef n env ++ indent n (show f ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    params = "(" ++ intercalate ", " args ++ ")"
    args = map (\v -> "@" ++ show v) as ++ map pprintPlace ks

pprintEnvDef :: Int -> EnvDef -> String
pprintEnvDef n (EnvDef tys free) = indent n $ "{" ++ intercalate ", " vars ++ "}\n"
  where
    vars = map (\v -> "@" ++ show v) tys ++ map pprintPlace free
