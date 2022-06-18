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
  , EnvDef(..)
  , Name(..)
  , prime
  , ValueC(..)
  , ArithC(..)
  , CmpC(..)
  , Sort(..)
  , ThunkType(..)
  , ProductType(..)
  , TypeDecls(..)

  , cconv
  , runConv
  , pprintThunkType
  , pprintTerm
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum, Product)

import Data.List (intercalate, partition)
import Data.Bifunctor

import qualified CPS as K
import CPS (TermK(..), FunDef(..), ContDef(..), ValueK(..), ArithK(..), CmpK(..))

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

-- | 'Sort' is really a simplified form of type information.
-- Value = int
-- Sum = bool | t1 + t2
-- Product = () | t1 * t2
-- Closure = (t1, t2, ...) -> 0
-- Alloc = a : *
-- Eventually, I may want to distinguish between named and anonymous product
-- types.
data Sort
  = Closure [Sort]
  -- TODO: Rename Sort.Value to Sort.Integer
  | Value
  | Alloc TyVar
  | Sum
  | Product [Sort]
  | Pair Sort Sort
  | Unit
  | Boolean
  | List Sort
  deriving (Eq, Ord)

instance Show Sort where
  show (Closure ss) = "closure " ++ show ss
  show Value = "value"
  show (Alloc aa) = "alloc"
  show Sum = "sum"
  show Boolean = "bool"
  show (Product ss) = "product " ++ show ss
  show (List s) = "list " ++ show s

sortOf :: K.TypeK -> Sort
sortOf (K.SumK _ _) = Sum
sortOf K.BoolK = Boolean
sortOf (K.ProdK t1 t2) = Pair (sortOf t1) (sortOf t2)
sortOf K.UnitK = Unit
sortOf K.IntK = Value
sortOf (K.ListK t) = List (sortOf t)
sortOf (K.FunK ts ss) = Closure (map sortOf ts ++ map coSortOf ss)

coSortOf :: K.CoTypeK -> Sort
coSortOf (K.ContK ss) = Closure (map sortOf ss)

-- | Each type of closure (e.g., one boxed argument, one unboxed argument and
-- one continuation, etc.) requires a different type of thunk when that closure
-- is opened. A thunk type specifies what arguments have been provided to the
-- closure.
--
-- 'Thunk' probably isn't the best name for this concept, as there is no
-- memoization/updating that occurs.
newtype ThunkType = ThunkType { thunkArgSorts :: [Sort] }
  deriving (Eq, Ord)

thunkTypesOf :: K.TypeK -> Set ThunkType
thunkTypesOf (K.FunK ts ss) =
  Set.insert (ThunkType (map sortOf ts ++ map coSortOf ss)) $
    Set.unions (map thunkTypesOf ts) <>
    Set.unions (map coThunkTypesOf ss)
thunkTypesOf (K.ProdK t s) = thunkTypesOf t <> thunkTypesOf s
thunkTypesOf (K.SumK t s) = thunkTypesOf t <> thunkTypesOf s
thunkTypesOf (K.ListK t) = thunkTypesOf t
thunkTypesOf K.UnitK = Set.empty
thunkTypesOf K.IntK = Set.empty
thunkTypesOf K.BoolK = Set.empty

coThunkTypesOf :: K.CoTypeK -> Set ThunkType
coThunkTypesOf (K.ContK ss) =
  Set.insert (ThunkType (map sortOf ss)) $ Set.unions (map thunkTypesOf ss)

productTypesOf :: K.TypeK -> Set ProductType
productTypesOf K.UnitK = Set.singleton (ProductType [])
productTypesOf (K.ProdK t s) =
  Set.insert (ProductType [sortOf t, sortOf s]) (productTypesOf t <> productTypesOf s)
productTypesOf (K.SumK t s) = productTypesOf t <> productTypesOf s
productTypesOf K.IntK = Set.empty
productTypesOf K.BoolK = Set.empty
productTypesOf (K.ListK t) = productTypesOf t
productTypesOf (K.FunK ts ss) =
  Set.unions (map productTypesOf ts) <> Set.unions (map coProductTypesOf ss)

coProductTypesOf :: K.CoTypeK -> Set ProductType
coProductTypesOf (K.ContK ss) = Set.unions (map productTypesOf ss)

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
  -- Invoke a closure by providing values for the remaining arguments.
  | JumpC Name [Name] -- k x...
  | CallC Name [Name] [Name] -- f x+ k+
  | HaltC Name
  | CaseC Name Sort [(Name, ThunkType)] -- case x of k1 | k2 | ...

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
    -- TODO: Have a name for the environment parameter
    -- (It makes things cleaner later on)
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

data EnvDef = EnvDef { envFreeNames :: [(Name, Sort)], envRecNames :: [(Name, Sort)] }

data ValueC
  = PairC Name Name
  | NilC
  | InlC Name
  | InrC Name
  | IntC Int
  | BoolC Bool
  | EmptyC
  | ConsC Name Name


-- TODO: Closure conversion should record free type variables as well.
-- I'm not entirely satisfied with the existence of 'FieldsFor'. It should be a
-- bottom-up traversal, just like the 'cconv' pass, but I end up separating it
-- out and repeatedly invoking it. (the time complexity is not correct.)
--
-- I think that the "proper" way to do it is with a Writer monad, and using
-- 'censor' to implement 'bindFields'? I might just keep it as part of the
-- return value, though.
newtype FieldsFor = FieldsFor { runFieldsFor :: Map Name Sort -> (Set (Name, Sort), Set TyVar) }

instance Semigroup FieldsFor where
  fs <> fs' = FieldsFor $ \ctx -> runFieldsFor fs ctx <> runFieldsFor fs' ctx

instance Monoid FieldsFor where
  mempty = FieldsFor $ \_ -> (Set.empty, Set.empty)

unitField :: Name -> FieldsFor
unitField x = FieldsFor $ \ctx -> case Map.lookup x ctx of
  Nothing -> error ("unbound variable occurrence: " ++ show x ++ " not in " ++ show ctx)
  Just s -> (Set.singleton (x, s), Set.empty)

unitTm :: K.TmVar -> FieldsFor
unitTm = unitField . tmVar

unitCo :: K.CoVar -> FieldsFor
unitCo = unitField . coVar

-- TODO: Implement 'unitTy'
unitTy :: () -> FieldsFor
unitTy () = mempty

bindFields :: [(Name, Sort)] -> FieldsFor -> FieldsFor
bindFields xs fs = FieldsFor $ \ctx ->
  let ctx' = foldr (uncurry Map.insert) ctx xs in
  let (fields, tys) = runFieldsFor fs ctx' in
  (fields Set.\\ Set.fromList xs, tys)

bindTm :: (K.TmVar, K.TypeK) -> (Name, Sort)
bindTm = bimap tmVar sortOf

bindCo :: (K.CoVar, K.CoTypeK) -> (Name, Sort)
bindCo = bimap coVar coSortOf


fieldsFor :: TermK a -> FieldsFor
fieldsFor (LetFunK fs e) =
  foldMap (bindFields fs' . fieldsForFunDef) fs <> bindFields fs' (fieldsFor e)
  where fs' = funDefNames fs
fieldsFor (LetContK ks e) =
  foldMap (bindFields ks' . fieldsForContDef) ks <> bindFields ks' (fieldsFor e)
  where ks' = contDefNames ks
fieldsFor (HaltK x) = unitTm x
fieldsFor (JumpK k xs) = unitCo k <> foldMap unitTm xs
fieldsFor (CallK f xs ks) = unitTm f <> foldMap unitTm xs <> foldMap unitCo ks
fieldsFor (CaseK x _ ks) = unitTm x <> foldMap unitCo ks
fieldsFor (LetFstK x t y e) =
  unitTm y <> fieldsForTy t <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetSndK x t y e) =
  unitTm y <> fieldsForTy t <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetValK x t v e) =
  fieldsForValue v <> fieldsForTy t <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetArithK x op e) = fieldsForArith op <> bindFields [(tmVar x, Value)] (fieldsFor e)
fieldsFor (LetNegateK x y e) = unitTm y <> bindFields [(tmVar x, Value)] (fieldsFor e)
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
  bindFields (map bindTm xs ++ map bindCo ks) (fieldsFor e)

fieldsForContDef :: ContDef a -> FieldsFor
fieldsForContDef (ContDef _ _k xs e) =
  bindFields (map bindTm xs) (fieldsFor e)

fieldsForTy :: K.TypeK -> FieldsFor
fieldsForTy K.UnitK = mempty
fieldsForTy K.IntK = mempty
fieldsForTy K.BoolK = mempty
fieldsForTy (K.ProdK t s) = fieldsForTy t <> fieldsForTy s
fieldsForTy (K.SumK t s) = fieldsForTy t <> fieldsForTy s
fieldsForTy (K.ListK t) = fieldsForTy t
fieldsForTy (K.FunK ts ss) = foldMap fieldsForTy ts <> foldMap fieldsForCoTy ss

fieldsForCoTy :: K.CoTypeK -> FieldsFor
fieldsForCoTy (K.ContK ss) = foldMap fieldsForTy ss

-- | Split occurrences into free variables and recursive calls.
-- Return @(free, rec)@.
markRec :: Set Name -> [(Name, Sort)] -> ([(Name, Sort)], [(Name, Sort)])
markRec fs xs = partition (\ (x, _) -> if Set.member x fs then False else True) xs

funDefNames :: [FunDef a] -> [(Name, Sort)]
funDefNames fs = [(tmVar f, Closure (map (sortOf . snd) xs ++ map (coSortOf . snd) ks)) | FunDef _ f xs ks _ <- fs]

contDefNames :: [ContDef a] -> [(Name, Sort)]
contDefNames ks = [(coVar k, Closure (map (sortOf . snd) xs)) | ContDef _ k xs _ <- ks]

newtype TypeDecls = TypeDecls { getTypeDecls :: (Set ThunkType, Set ProductType) }

deriving newtype instance Semigroup TypeDecls
deriving newtype instance Monoid TypeDecls

-- Note: Currently, ProductType only deals with tuple types, which do not have
-- named fields. In the future, if/when I have records (named or anonymous?), I
-- should probably have a second type that describes named product types.
newtype ProductType = ProductType [Sort]
  deriving (Eq, Ord)

-- TODO: Collecting type declarations should be done in Hoist, I think.
-- Idea: map anonymous record/closure types to numerically-named ones
-- 'product_17', 'closure_32', etc. Just makes the type names shorter and
-- potentially more uniform with named types.
newtype ConvM a = ConvM { runConvM :: ReaderT (Map Name Sort) (Writer TypeDecls) a }

deriving newtype instance Functor ConvM
deriving newtype instance Applicative ConvM
deriving newtype instance Monad ConvM
deriving newtype instance MonadReader (Map Name Sort) ConvM
deriving newtype instance MonadWriter TypeDecls ConvM

runConv :: ConvM a -> (a, TypeDecls)
runConv = runWriter . flip runReaderT Map.empty . runConvM

-- Idea: I could factor out the fieldsFor computation by doing a first
-- annotation pass over the data, and then having
-- 'cconv :: TermK EnvFields -> ConvM TermC'
-- This does get a bit messy with both TmVar/CoVar and Name being present,
-- though.
cconv :: TermK a -> ConvM TermC
cconv (LetFunK fs e) =
  LetFunC <$> local extendGroup (traverse (cconvFunDef fs') fs) <*> local extendGroup (cconv e)
  where
    fs' = Set.fromList (fst <$> funDefNames fs)
    extendGroup ctx = foldr (uncurry Map.insert) ctx (funDefNames fs)
cconv (LetContK ks e) =
  LetContC <$> local extendGroup (traverse (cconvContDef ks') ks) <*> local extendGroup (cconv e)
  where
    ks' = Set.fromList (fst <$> contDefNames ks)
    extendGroup ctx = foldr (uncurry Map.insert) ctx (contDefNames ks)
cconv (HaltK x) = pure $ HaltC (tmVar x)
cconv (JumpK k xs) = pure $ JumpC (coVar k) (map tmVar xs)
cconv (CallK f xs ks) = pure $ CallC (tmVar f) (map tmVar xs) (map coVar ks)
cconv (CaseK x t ks) = do
  tell (TypeDecls (mempty, productTypesOf t))
  -- The type of each thunk/branch is determined by the type of the scrutinee.
  let
    ks' = case t of
      K.SumK a b -> zip (map coVar ks) [ThunkType [sortOf a], ThunkType [sortOf b]]
      K.BoolK -> zip (map coVar ks) [ThunkType [], ThunkType []]
      K.ListK a -> zip (map coVar ks) [ThunkType [], ThunkType [sortOf a, sortOf t]]
      _ -> error "cannot case on this type"
  pure $ CaseC (tmVar x) (sortOf t) ks'
cconv (LetFstK x t y e) = LetFstC (tmVar x, sortOf t) (tmVar y) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) (sortOf t) ctx
cconv (LetSndK x t y e) = LetSndC (tmVar x, sortOf t) (tmVar y) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) (sortOf t) ctx
cconv (LetValK x t v e) = LetValC (tmVar x, sortOf t) <$> cconvValue v <*> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) (sortOf t) ctx
cconv (LetArithK x op e) = LetArithC (tmVar x, Value) (cconvArith op) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) Value ctx
cconv (LetNegateK x y e) = LetNegateC (tmVar x, Value) (tmVar y) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) Value ctx
cconv (LetCompareK x cmp e) = LetCompareC (tmVar x, Boolean) (cconvCmp cmp) <$> local extend (cconv e)
  where
    extend ctx = Map.insert (tmVar x) Boolean ctx

cconvFunDef :: Set Name -> FunDef a -> ConvM FunClosureDef
cconvFunDef fs fun@(FunDef _ f xs ks e) = do
  let
    funThunk = ThunkType (map (sortOf . snd) xs ++ map (coSortOf . snd) ks)
    thunks = Set.insert funThunk $ foldMap (thunkTypesOf . snd) xs <> foldMap (coThunkTypesOf . snd) ks
    products = foldMap (productTypesOf . snd) xs <> foldMap (coProductTypesOf . snd) ks
  tell (TypeDecls (thunks, products))
  let tmbinds = map bindTm xs
  let cobinds = map bindCo ks
  let extend ctx' = foldr (uncurry Map.insert) ctx' (tmbinds ++ cobinds)
  (fields, tyfields) <- fmap (runFieldsFor (fieldsForFunDef fun) . extend) ask
  -- Idea: Make closure environments be anonymous product types?
  -- Hmm, maybe not. That would lead to anonymous polymorphic products, which
  -- I'm not quite sure on implementing.
  let (free, rec) = markRec fs (Set.toList fields)
  e' <- local extend (cconv e)
  pure (FunClosureDef (tmVar f) (EnvDef free rec) tmbinds cobinds e')

cconvContDef :: Set Name -> ContDef a -> ConvM ContClosureDef
cconvContDef ks kont@(ContDef _ k xs e) = do
  let
    contThunk = ThunkType (map (sortOf . snd) xs)
    thunks = Set.insert contThunk $ foldMap thunkTypesOf (map snd xs)
    products = foldMap productTypesOf (map snd xs)
  tell (TypeDecls (thunks, products))
  let binds = map bindTm xs
  let extend ctx' = foldr (uncurry Map.insert) ctx' binds
  (fields, tyfields) <- fmap (runFieldsFor (fieldsForContDef kont) . extend) ask
  let (free, rec) = markRec ks (Set.toList fields)
  e' <- local extend (cconv e)
  pure (ContClosureDef (coVar k) (EnvDef free rec) binds e')

cconvValue :: ValueK -> ConvM ValueC
cconvValue NilK = do
  tell (TypeDecls (mempty, Set.singleton (ProductType [])))
  pure NilC
cconvValue (PairK x y) = do
  ctx <- ask
  let sx = ctx Map.! (tmVar x)
  let sy = ctx Map.! (tmVar y)
  tell (TypeDecls (mempty, Set.singleton (ProductType [sx, sy])))
  pure (PairC (tmVar x) (tmVar y))
cconvValue (IntValK i) = pure (IntC i)
cconvValue (BoolValK b) = pure (BoolC b)
cconvValue (InlK x) = pure (InlC (tmVar x))
cconvValue (InrK y) = pure (InrC (tmVar y))
cconvValue EmptyK = pure EmptyC
cconvValue (ConsK x y) = pure (ConsC (tmVar x) (tmVar y))

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

pprintThunkType :: ThunkType -> String
pprintThunkType (ThunkType ss) = "thunk (" ++ intercalate ", " (map show ss) ++ ") -> !\n"

pprintTerm :: Int -> TermC -> String
pprintTerm n (HaltC x) = indent n $ "HALT " ++ show x ++ ";\n"
pprintTerm n (JumpC k xs) = indent n $ show k ++ " " ++ intercalate " " (map show xs) ++ ";\n"
pprintTerm n (CallC f xs ks) = indent n $ show f ++ " " ++ intercalate " " (map show xs ++ map show ks) ++ ";\n"
pprintTerm n (LetFunC fs e) =
  indent n "letfun\n" ++ concatMap (pprintClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
pprintTerm n (LetContC fs e) =
  indent n "letcont\n" ++ concatMap (pprintContClosureDef (n+2)) fs ++ indent n "in\n" ++ pprintTerm n e
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

pprintClosureDef :: Int -> FunClosureDef -> String
pprintClosureDef n (FunClosureDef f env xs ks e) =
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

pprintEnvDef :: Int -> EnvDef -> String
pprintEnvDef n (EnvDef free rec) = indent n $ "{" ++ intercalate ", " vars ++ "}\n"
  where
    vars = map (\ (v, s) -> show s ++ " " ++ show v) (free ++ rec)
