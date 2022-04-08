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
  , ContClosureDef(..)
  , Name(..)
  , prime
  , ValueC(..)
  , ArithC(..)
  , CmpC(..)
  , Sort(..)
  , ThunkType(..)

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
import Control.Monad.Writer hiding (Sum)

import Data.List (intercalate, partition)
import Data.Maybe (mapMaybe)
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
coVar (K.CoVar k) = Name k 0

-- | 'Sort' is really a simplified form of type information.
-- Value = int | bool | t1 * t2 | t1 + t2 | ()
-- Closure = (t1, t2, ...) -> 0
-- Alloc = a : *
data Sort = Closure | Value | Alloc | Sum
  deriving (Eq, Ord)

instance Show Sort where
  show Closure = "closure"
  show Value = "value"
  show Alloc = "alloc_header"
  show Sum = "sum"

sortOf :: K.TypeK -> Sort
sortOf (K.ContK _) = Closure
sortOf (K.FunK _ _) = Closure
sortOf (K.SumK _ _) = Sum
sortOf K.BoolK = Sum
sortOf _ = Value

-- | Each type of closure (e.g., one boxed argument, one unboxed argument and
-- one continuation, etc.) requires a different type of thunk when that closure
-- is opened. A thunk type specifies what arguments have been provided to the
-- closure.
newtype ThunkType = ThunkType { thunkArgSorts :: [Sort] }
  deriving (Eq, Ord)

thunkTypeOf :: K.TypeK -> Maybe ThunkType
thunkTypeOf (K.ContK ss) = Just (ThunkType (map sortOf ss))
thunkTypeOf (K.FunK t s) = Just (ThunkType [sortOf t, sortOf (K.ContK [s])])
thunkTypeOf _ = Nothing

-- Closure conversion is bottom-up (to get flat closures) traversal that
-- replaces free variables with references to an environment parameter.
data TermC
  = LetValC (Name, Sort) ValueC TermC -- let x = v in e, allocation
  | LetFstC (Name, Sort) Name TermC -- let x = fst y in e, projection
  | LetSndC (Name, Sort) Name TermC
  | LetArithC (Name, Sort) ArithC TermC
  | LetCompareC (Name, Sort) CmpC TermC
  | LetFunC [FunClosureDef] TermC
  | LetContC [ContClosureDef] TermC
  -- Invoke a closure by providing a value for the only remaining argument.
  | JumpC Name [Name] -- k x...
  | CallC Name [Name] [Name] -- f x+ k+
  | HaltC Name
  | CaseC Name [(Name, ThunkType)] -- case x of k1 | k2 | ...

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

-- | @f {x+} y k = e@
-- Closures capture two sets of names: those from outer scopes, and those from
-- the same recursive bind group.
data FunClosureDef
  = FunClosureDef {
    funClosureName :: Name
  , funClosureFreeNames :: [(Name, Sort)]
  , funClosureRecNames :: [(Name, Sort)]
  , funClosureParam :: [(Name, Sort)]
  , funClosureCont :: [(Name, Sort)]
  , funClosureBody :: TermC
  }

-- | @k {x+} y = e@
-- Closures capture two sets of names: those from outer scopes, and those from
-- the same recursive bind group.
data ContClosureDef
  = ContClosureDef {
    contClosureName :: Name
  , contClosureFreeNames :: [(Name, Sort)]
  , contClosureRecNames :: [(Name, Sort)]
  , contClosureParam :: [(Name, Sort)]
  , contClosureBody :: TermC
  }

data ValueC
  = PairC Name Name
  | InlC Name
  | InrC Name
  | NilC
  | IntC Int
  | BoolC Bool


newtype FieldsFor = FieldsFor { runFieldsFor :: Map Name Sort -> Set (Name, Sort) }

instance Semigroup FieldsFor where
  fs <> fs' = FieldsFor $ \ctx -> runFieldsFor fs ctx <> runFieldsFor fs' ctx

instance Monoid FieldsFor where
  mempty = FieldsFor $ \_ -> Set.empty

unitField :: Name -> FieldsFor
unitField x = FieldsFor $ \ctx -> case Map.lookup x ctx of
  Nothing -> error ("unbound variable occurrence: " ++ show x ++ " not in " ++ show ctx)
  Just s -> Set.singleton (x, s)

bindFields :: [(Name, Sort)] -> FieldsFor -> FieldsFor
bindFields xs fs = FieldsFor $ \ctx ->
  let fields = runFieldsFor fs (foldr (uncurry Map.insert) ctx xs) in
  fields Set.\\ Set.fromList xs


fieldsFor :: TermK a -> FieldsFor
fieldsFor (LetFunK fs e) =
  foldMap (bindFields fs' . fieldsForFunDef) fs <> bindFields fs' (fieldsFor e)
  where fs' = funDefNames fs
fieldsFor (LetContK ks e) =
  foldMap (bindFields ks' . fieldsForContDef) ks <> bindFields ks' (fieldsFor e)
  where ks' = contDefNames ks
fieldsFor (HaltK x) = unitField (tmVar x)
fieldsFor (JumpK k xs) = unitField (coVar k) <> foldMap (unitField . tmVar) xs
fieldsFor (CallK f xs ks) =
  unitField (tmVar f) <>
  foldMap (unitField . tmVar) xs <>
  foldMap (unitField . coVar) ks
fieldsFor (CaseK x k1 _s1 k2 _s2) = unitField (tmVar x) <> unitField (coVar k1) <> unitField (coVar k2)
fieldsFor (LetFstK x t y e) = unitField (tmVar y) <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetSndK x t y e) = unitField (tmVar y) <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetValK x t v e) = fieldsForValue v <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetArithK x op e) = fieldsForArith op <> bindFields [(tmVar x, Value)] (fieldsFor e)
fieldsFor (LetCompareK x cmp e) = fieldsForCmp cmp <> bindFields [(tmVar x, Sum)] (fieldsFor e)

fieldsForArith :: ArithK -> FieldsFor
fieldsForArith (AddK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForArith (SubK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForArith (MulK x y) = unitField (tmVar x) <> unitField (tmVar y)

fieldsForCmp :: CmpK -> FieldsFor
fieldsForCmp (CmpEqK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForCmp (CmpNeK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForCmp (CmpLtK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForCmp (CmpLeK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForCmp (CmpGtK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForCmp (CmpGeK x y) = unitField (tmVar x) <> unitField (tmVar y)

fieldsForValue :: ValueK -> FieldsFor
fieldsForValue (IntValK _) = mempty
fieldsForValue (BoolValK _) = mempty
fieldsForValue NilK = mempty
fieldsForValue (PairK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForValue (InlK x) = unitField (tmVar x)
fieldsForValue (InrK y) = unitField (tmVar y)

fieldsForFunDef :: FunDef a -> FieldsFor
fieldsForFunDef (FunDef _ _f xs ks e) =
  bindFields (map (bimap tmVar sortOf) xs ++ map (bimap coVar sortOf) ks) (fieldsFor e)

fieldsForContDef :: ContDef a -> FieldsFor
fieldsForContDef (ContDef _ _k xs e) =
  bindFields (map (bimap tmVar sortOf) xs) (fieldsFor e)

-- | Split occurrences into free variables and recursive calls.
-- Return @(free, rec)@.
markRec :: Set Name -> [(Name, Sort)] -> ([(Name, Sort)], [(Name, Sort)])
markRec fs xs = partition (\ (x, _) -> if Set.member x fs then False else True) xs

funDefNames :: [FunDef a] -> [(Name, Sort)]
funDefNames fs = [(tmVar f, Closure) | FunDef _ f _ _ _ <- fs]

contDefNames :: [ContDef a] -> [(Name, Sort)]
contDefNames ks = [(coVar k, Closure) | ContDef _ k _ _ <- ks]

newtype ConvM a = ConvM { runConvM :: ReaderT (Map Name Sort) (Writer (Set ThunkType)) a }

deriving newtype instance Functor ConvM
deriving newtype instance Applicative ConvM
deriving newtype instance Monad ConvM
deriving newtype instance MonadReader (Map Name Sort) ConvM
deriving newtype instance MonadWriter (Set ThunkType) ConvM

runConv :: ConvM a -> (a, Set ThunkType)
runConv = runWriter . flip runReaderT Map.empty . runConvM

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
cconv (CaseK x k1 s1 k2 s2) = do
  let
    ann :: (K.CoVar, K.TypeK) -> Maybe (Name, ThunkType)
    ann (k, s) = do
      t <- thunkTypeOf s
      pure (coVar k, t)
  ks' <- case traverse ann [(k1, s1), (k2, s2)] of
    Just ks' -> pure ks'
    -- TODO: Better panic info: which branch isn't a thunk?
    Nothing -> error "cconv: some branch of case is not a closure"
  pure $ CaseC (tmVar x) ks'
cconv (LetFstK x t y e) = LetFstC (tmVar x, sortOf t) (tmVar y) <$> cconv e
cconv (LetSndK x t y e) = LetSndC (tmVar x, sortOf t) (tmVar y) <$> cconv e
cconv (LetValK x t v e) = LetValC (tmVar x, sortOf t) (cconvValue v) <$> cconv e
cconv (LetArithK x op e) = LetArithC (tmVar x, Value) (cconvArith op) <$> cconv e
cconv (LetCompareK x cmp e) = LetCompareC (tmVar x, Sum) (cconvCmp cmp) <$> cconv e

cconvFunDef :: Set Name -> FunDef a -> ConvM FunClosureDef
cconvFunDef fs fun@(FunDef _ f xs ks e) = do
  let
    funThunk = ThunkType (map (sortOf . snd) xs ++ map (sortOf . snd) ks)
    thunks = funThunk : mapMaybe thunkTypeOf (map snd xs ++ map snd ks)
  tell (Set.fromList thunks)
  let tmbinds = map (bimap tmVar sortOf) xs
  let cobinds = map (bimap coVar sortOf) ks
  let extend ctx' = foldr (uncurry Map.insert) ctx' (tmbinds ++ cobinds)
  fields <- fmap (runFieldsFor (fieldsForFunDef fun) . extend) ask
  let (free, rec) = markRec fs (Set.toList fields)
  e' <- local extend (cconv e)
  pure (FunClosureDef (tmVar f) free rec tmbinds cobinds e')

cconvContDef :: Set Name -> ContDef a -> ConvM ContClosureDef
cconvContDef ks kont@(ContDef _ k xs e) = do
  let
    contThunk = ThunkType (map (sortOf . snd) xs)
    thunks = contThunk : mapMaybe thunkTypeOf (map snd xs)
  tell (Set.fromList thunks)
  let binds = map (bimap tmVar sortOf) xs
  let extend ctx' = foldr (uncurry Map.insert) ctx' binds
  fields <- fmap (runFieldsFor (fieldsForContDef kont) . extend) ask
  let (free, rec) = markRec ks (Set.toList fields)
  e' <- local extend (cconv e)
  pure (ContClosureDef (coVar k) free rec binds e')

cconvValue :: ValueK -> ValueC
cconvValue NilK = NilC
cconvValue (PairK x y) = PairC (tmVar x) (tmVar y)
cconvValue (IntValK i) = IntC i
cconvValue (BoolValK b) = BoolC b
cconvValue (InlK x) = InlC (tmVar x)
cconvValue (InrK y) = InrC (tmVar y)

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
pprintTerm n (CaseC x ks) =
  let branches = intercalate " | " (map (show . fst) ks) in
  indent n $ "case " ++ show x ++ " of " ++ branches ++ ";\n"
pprintTerm n (LetArithC x op e) =
  indent n ("let " ++ pprintPlace x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e
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
pprintClosureDef n (FunClosureDef f free rec xs ks e) =
  indent n env ++ indent n (show f ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    env = "{" ++ intercalate ", " vars ++ "}\n"
    vars = map (\ (v, s) -> show s ++ " " ++ show v) (free ++ rec)
    params = "(" ++ intercalate ", " args ++ ")"
    args = map pprintPlace xs ++ map pprintPlace ks

pprintContClosureDef :: Int -> ContClosureDef -> String
pprintContClosureDef n (ContClosureDef k free rec xs e) =
  indent n env ++ indent n (show k ++ " " ++ params ++ " =\n") ++ pprintTerm (n+2) e
  where
    env = "{" ++ intercalate ", " vars ++ "}\n"
    vars = map (\ (v, s) -> show s ++ " " ++ show v) (free ++ rec)
    params = "(" ++ intercalate ", " args ++ ")"
    args = map pprintPlace xs
