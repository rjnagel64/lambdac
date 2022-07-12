{-# LANGUAGE
    DerivingStrategies
  , GeneralizedNewtypeDeriving
  , StandaloneDeriving
  , FlexibleInstances
  , MultiParamTypeClasses
  #-}

module CC
  ( TermC(..)
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
import Data.List (intercalate, partition)
import Data.Bifunctor
import Prelude hiding (abs)

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
-- TODO: Parametrize 'Sort' by type of variable?: 'Sort TyVar' and 'Sort DBLevel'
-- TODO: 'Sort.Info' is the odd one out, often times. Make it more uniform, somehow.
data Sort
  = Closure [Sort]
  | Integer
  | Alloc TyVar
  -- TODO: It doesn't make sense for Info to be a sort; you can't make a pair of info
  | Info TyVar
  | Sum
  | Pair Sort Sort
  | Unit
  | Boolean
  | List Sort
  deriving (Eq, Ord)

instance Show Sort where
  show (Closure ss) = "closure " ++ show ss
  show Integer = "value"
  show (Alloc aa) = "alloc"
  show (Info aa) = "info"
  show Sum = "sum"
  show Boolean = "bool"
  show (List s) = "list " ++ show s
  show (Pair s t) = "pair " ++ show s ++ " " ++ show t
  show Unit = "unit"

sortOf :: K.TypeK -> Sort
sortOf (K.SumK _ _) = Sum
sortOf K.BoolK = Boolean
sortOf (K.ProdK t1 t2) = Pair (sortOf t1) (sortOf t2)
sortOf K.UnitK = Unit
sortOf K.IntK = Integer
sortOf (K.ListK t) = List (sortOf t)
sortOf (K.FunK ts ss) = Closure (map sortOf ts ++ map coSortOf ss)
sortOf (K.TyVarOccK aa) = Alloc (tyVar aa)
sortOf (K.AllK aas ss) = Closure (map coSortOf ss) -- TODO: 'Closure' is insufficient

coSortOf :: K.CoTypeK -> Sort
coSortOf (K.ContK ss) = Closure (map sortOf ss)

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
  | CaseC Name Sort [(Name, BranchType)] -- case x of k1 | k2 | ...
  | InstC Name [Sort] [Name] -- f @t+ k+

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
funClosureSort (FunClosureDef _ _ params conts _) = Closure (map snd params ++ map snd conts)

-- | @k {x+} y+ = e@
-- Closures capture two sets of names: those from outer scopes, and those from
-- the same recursive bind group.
data ContClosureDef
  = ContClosureDef {
    contClosureName :: Name
  , contEnvDef :: EnvDef
  , contClosureParams :: [(Name, Sort)]
  , contClosureBody :: TermC
  }

contClosureSort :: ContClosureDef -> Sort
contClosureSort (ContClosureDef _ _ params _) = Closure (map snd params)

data AbsClosureDef
  = AbsClosureDef {
    absClosureName :: Name
  , absEnvDef :: EnvDef
  , absClosureTypes :: [TyVar]
  , absClosureConts :: [(Name, Sort)]
  , absClosureBody :: TermC
  }

absClosureSort :: AbsClosureDef -> Sort
absClosureSort (AbsClosureDef _ _ types conts _) = Closure (map snd conts)

data EnvDef
  = EnvDef {
    envFreeTypes :: [TyVar]
  , envFreeNames :: [(Name, Sort)]
  , envRecNames :: [(Name, Sort)]
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

-- TODO: Closure conversion should record free type variables as well.
-- I'm not entirely satisfied with the existence of 'FieldsFor'. It should be a
-- bottom-up traversal, just like the 'cconv' pass, but I end up separating it
-- out and repeatedly invoking it. (the time complexity is not correct.)
--
-- I think that the "proper" way to do it is with a Writer monad, and using
-- 'censor' to implement 'bindFields'? I might just keep it as part of the
-- return value, though.
newtype FieldsFor = FieldsFor { runFieldsFor :: Map Name Sort -> (Set FreeOcc, Set TyVar) }

instance Semigroup FieldsFor where
  fs <> fs' = FieldsFor $ \ctx -> runFieldsFor fs ctx <> runFieldsFor fs' ctx

instance Monoid FieldsFor where
  mempty = FieldsFor $ \_ -> (Set.empty, Set.empty)

unitField :: Name -> FieldsFor
unitField x = FieldsFor $ \ctx -> case Map.lookup x ctx of
  Nothing -> error ("unbound variable occurrence: " ++ show x ++ " not in " ++ show ctx)
  Just s -> (Set.singleton (FreeOcc x s), Set.empty)

unitTm :: K.TmVar -> FieldsFor
unitTm = unitField . tmVar

unitCo :: K.CoVar -> FieldsFor
unitCo = unitField . coVar

unitTy :: K.TyVar -> FieldsFor
unitTy aa = let aa' = tyVar aa in FieldsFor $ \ctx -> (Set.empty, Set.singleton aa')

bindFields :: [(Name, Sort)] -> FieldsFor -> FieldsFor
bindFields xs fs = FieldsFor $ \ctx ->
  let ctx' = foldr (uncurry Map.insert) ctx xs in
  let (fields, tys) = runFieldsFor fs ctx' in
  (fields Set.\\ Set.fromList (uncurry FreeOcc <$> xs), tys)

bindTyFields :: [TyVar] -> FieldsFor -> FieldsFor
bindTyFields aas fs = FieldsFor $ \ctx ->
  let (fields, tys) = runFieldsFor fs ctx in
  (fields, tys Set.\\ Set.fromList aas)

bindTm :: (K.TmVar, K.TypeK) -> (Name, Sort)
bindTm = bimap tmVar sortOf

bindCo :: (K.CoVar, K.CoTypeK) -> (Name, Sort)
bindCo = bimap coVar coSortOf

bindTy :: K.TyVar -> TyVar
bindTy = tyVar


fieldsFor :: TermK a -> FieldsFor
fieldsFor (LetFunK fs e) =
  foldMap (bindFields fs' . fieldsForFunDef) fs <> bindFields fs' (fieldsFor e)
  where fs' = funDefNames fs
fieldsFor (LetContK ks e) =
  foldMap (bindFields ks' . fieldsForContDef) ks <> bindFields ks' (fieldsFor e)
  where ks' = contDefNames ks
fieldsFor (LetAbsK fs e) =
  foldMap (bindFields fs' . fieldsForAbsDef) fs <> bindFields fs' (fieldsFor e)
  where fs' = absDefNames fs
fieldsFor (HaltK x) = unitTm x
fieldsFor (JumpK k xs) = unitCo k <> foldMap unitTm xs
fieldsFor (CallK f xs ks) = unitTm f <> foldMap unitTm xs <> foldMap unitCo ks
fieldsFor (CaseK x _ ks) = unitTm x <> foldMap unitCo ks
fieldsFor (InstK f ts ks) = unitTm f <> foldMap fieldsForTy ts <> foldMap unitCo ks
fieldsFor (LetFstK x t y e) =
  unitTm y <> fieldsForTy t <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetSndK x t y e) =
  unitTm y <> fieldsForTy t <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetValK x t v e) =
  fieldsForValue v <> fieldsForTy t <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetArithK x op e) = fieldsForArith op <> bindFields [(tmVar x, Integer)] (fieldsFor e)
fieldsFor (LetNegateK x y e) = unitTm y <> bindFields [(tmVar x, Integer)] (fieldsFor e)
fieldsFor (LetCompareK x cmp e) = fieldsForCmp cmp <> bindFields [(tmVar x, Boolean)] (fieldsFor e)

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
  bindFields (map bindTm xs ++ map bindCo ks) (fieldsFor e) <>
  foldMap (fieldsForTy . snd) xs <>
  foldMap (fieldsForCoTy . snd) ks

fieldsForContDef :: ContDef a -> FieldsFor
fieldsForContDef (ContDef _ _k xs e) =
  bindFields (map bindTm xs) (fieldsFor e) <>
  foldMap (fieldsForTy . snd) xs

fieldsForAbsDef :: AbsDef a -> FieldsFor
fieldsForAbsDef (AbsDef _ _f as ks e) =
  bindTyFields (map bindTy as) $
    foldMap (fieldsForCoTy . snd) ks <>
    bindFields (map bindCo ks) (fieldsFor e)

fieldsForTy :: K.TypeK -> FieldsFor
fieldsForTy K.UnitK = mempty
fieldsForTy K.IntK = mempty
fieldsForTy K.BoolK = mempty
fieldsForTy (K.ProdK t s) = fieldsForTy t <> fieldsForTy s
fieldsForTy (K.SumK t s) = fieldsForTy t <> fieldsForTy s
fieldsForTy (K.ListK t) = fieldsForTy t
fieldsForTy (K.FunK ts ss) = foldMap fieldsForTy ts <> foldMap fieldsForCoTy ss
fieldsForTy (K.TyVarOccK aa) = unitTy aa
fieldsForTy (K.AllK aas ss) = bindTyFields (map bindTy aas) (foldMap fieldsForCoTy ss)

fieldsForCoTy :: K.CoTypeK -> FieldsFor
fieldsForCoTy (K.ContK ss) = foldMap fieldsForTy ss

-- | Split occurrences into free variables and recursive calls.
-- Return @(free, rec)@.
markRec :: Set Name -> [FreeOcc] -> ([(Name, Sort)], [(Name, Sort)])
markRec fs xs = partition (\ (x, _) -> if Set.member x fs then False else True) (map freeOcc xs)

funDefNames :: [FunDef a] -> [(Name, Sort)]
funDefNames fs = [(tmVar f, Closure (map (sortOf . snd) xs ++ map (coSortOf . snd) ks)) | FunDef _ f xs ks _ <- fs]

contDefNames :: [ContDef a] -> [(Name, Sort)]
contDefNames ks = [(coVar k, Closure (map (sortOf . snd) xs)) | ContDef _ k xs _ <- ks]

-- TODO: What is the sort of a polymorphic function? 'Closure' is insufficient.
absDefNames :: [AbsDef a] -> [(Name, Sort)]
absDefNames fs = [(tmVar f, Closure (map (coSortOf . snd) ks)) | AbsDef _ f as ks _ <- fs]

newtype ConvM a = ConvM { runConvM :: Reader (Map Name Sort) a }

deriving newtype instance Functor ConvM
deriving newtype instance Applicative ConvM
deriving newtype instance Monad ConvM
deriving newtype instance MonadReader (Map Name Sort) ConvM

runConv :: ConvM a -> a
runConv = flip runReader Map.empty . runConvM

-- Idea: I could factor out the fieldsFor computation by doing a first
-- annotation pass over the data, and then having
-- 'cconv :: TermK EnvFields -> ConvM TermC'
-- This does get a bit messy with both TmVar/CoVar and Name being present,
-- though.
cconv :: TermK a -> ConvM TermC
cconv (LetFunK fs e) =
  let names = funDefNames fs in
  let fs' = Set.fromList (fst <$> names) in
  let extendGroup ctx = foldr (uncurry Map.insert) ctx names in
  LetFunC <$> local extendGroup (traverse (cconvFunDef fs') fs) <*> local extendGroup (cconv e)
cconv (LetContK ks e) =
  let names = contDefNames ks in
  let ks' = Set.fromList (fst <$> names) in
  let extend ctx = foldr (uncurry Map.insert) ctx names in
  LetContC <$> local extend (traverse (cconvContDef ks') ks) <*> local extend (cconv e)
cconv (LetAbsK fs e) =
  let names = absDefNames fs in
  let extend ctx = foldr (uncurry Map.insert) ctx names in
  let fs' = Set.fromList (fst <$> names) in
  LetAbsC <$> local extend (traverse (cconvAbsDef fs') fs) <*> local extend (cconv e)
cconv (HaltK x) = pure $ HaltC (tmVar x)
cconv (JumpK k xs) = pure $ JumpC (coVar k) (map tmVar xs)
cconv (CallK f xs ks) = pure $ CallC (tmVar f) (map tmVar xs) (map coVar ks)
cconv (CaseK x t ks) = do
  -- The type of each thunk/branch is determined by the type of the scrutinee.
  let
    ks' = case t of
      K.SumK a b -> zip (map coVar ks) [BranchType [sortOf a], BranchType [sortOf b]]
      K.BoolK -> zip (map coVar ks) [BranchType [], BranchType []]
      K.ListK a -> zip (map coVar ks) [BranchType [], BranchType [sortOf a, sortOf t]]
      _ -> error "cannot case on this type"
  pure $ CaseC (tmVar x) (sortOf t) ks'
cconv (InstK f ts ks) = pure $ InstC (tmVar f) (map sortOf ts) (map coVar ks)
cconv (LetFstK x t y e) = LetFstC (tmVar x, sortOf t) (tmVar y) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) (sortOf t) ctx
cconv (LetSndK x t y e) = LetSndC (tmVar x, sortOf t) (tmVar y) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) (sortOf t) ctx
cconv (LetValK x t v e) = LetValC (tmVar x, sortOf t) (cconvValue v) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) (sortOf t) ctx
cconv (LetArithK x op e) = LetArithC (tmVar x, Integer) (cconvArith op) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) Integer ctx
cconv (LetNegateK x y e) = LetNegateC (tmVar x, Integer) (tmVar y) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) Integer ctx
cconv (LetCompareK x cmp e) = LetCompareC (tmVar x, Boolean) (cconvCmp cmp) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) Boolean ctx

cconvFunDef :: Set Name -> FunDef a -> ConvM FunClosureDef
cconvFunDef fs fun@(FunDef _ f xs ks e) = do
  let tmbinds = map bindTm xs
  let cobinds = map bindCo ks
  let extend ctx' = foldr (uncurry Map.insert) ctx' (tmbinds ++ cobinds)
  (fields, tyfields) <- fmap (runFieldsFor (fieldsForFunDef fun) . extend) ask
  let (free, rec) = markRec fs (Set.toList fields)
  e' <- local extend (cconv e)
  pure (FunClosureDef (tmVar f) (EnvDef (Set.toList tyfields) free rec) tmbinds cobinds e')

cconvContDef :: Set Name -> ContDef a -> ConvM ContClosureDef
cconvContDef ks kont@(ContDef _ k xs e) = do
  let tmbinds = map bindTm xs
  let extend ctx' = foldr (uncurry Map.insert) ctx' tmbinds
  (fields, tyfields) <- fmap (runFieldsFor (fieldsForContDef kont) . extend) ask
  let (free, rec) = markRec ks (Set.toList fields)
  e' <- local extend (cconv e)
  pure (ContClosureDef (coVar k) (EnvDef (Set.toList tyfields) free rec) tmbinds e')

cconvAbsDef :: Set Name -> AbsDef a -> ConvM AbsClosureDef
cconvAbsDef fs abs@(AbsDef _ f as ks e) = do
  let tybinds = map bindTy as
  let cobinds = map bindCo ks
  let extend ctx' = foldr (uncurry Map.insert) ctx' cobinds
  (fields, tyfields) <- fmap (runFieldsFor (fieldsForAbsDef abs) . extend) ask
  let (free, rec) = markRec fs (Set.toList fields)
  e' <- local extend (cconv e)
  pure (AbsClosureDef (tmVar f) (EnvDef (Set.toList tyfields) free rec) tybinds cobinds e')

cconvValue :: ValueK -> ValueC
cconvValue NilK = NilC
cconvValue (PairK x y) = (PairC (tmVar x) (tmVar y))
cconvValue (IntValK i) = (IntC i)
cconvValue (BoolValK b) = (BoolC b)
cconvValue (InlK x) = (InlC (tmVar x))
cconvValue (InrK y) = (InrC (tmVar y))
cconvValue EmptyK = EmptyC
cconvValue (ConsK x y) = (ConsC (tmVar x) (tmVar y))

cconvArith :: ArithK -> ArithC
cconvArith (AddK x y) = AddC (tmVar x) (tmVar y)
cconvArith (SubK x y) = SubC (tmVar x) (tmVar y)
cconvArith (MulK x y) = MulC (tmVar x) (tmVar y)

cconvCmp :: CmpK -> CmpC
cconvCmp (CmpEqK x y) = EqC (tmVar x) (tmVar y)
cconvCmp (CmpNeK x y) = NeC (tmVar x) (tmVar y)
cconvCmp (CmpLtK x y) = LtC (tmVar x) (tmVar y)
cconvCmp (CmpLeK x y) = LeC (tmVar x) (tmVar y)
cconvCmp (CmpGtK x y) = GtC (tmVar x) (tmVar y)
cconvCmp (CmpGeK x y) = GeC (tmVar x) (tmVar y)

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
  let branches = intercalate " | " (map (show . fst) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetArithC x op e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetNegateC x y e) =
  indent n ("let " ++ pprintPlace x ++ " = -" ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (LetCompareC x cmp e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintCompare cmp ++ ";\n") ++ pprintTerm n e

pprintPlace :: (Name, Sort) -> String
pprintPlace (x, s) = show s ++ " " ++ show x

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
pprintEnvDef n (EnvDef tys free rec) = indent n $ "{" ++ intercalate ", " vars ++ "}\n"
  where
    vars = map (\v -> "@" ++ show v) tys ++ map (\ (v, s) -> show s ++ " " ++ show v) (free ++ rec)
