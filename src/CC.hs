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
  , ValueC(..)
  , ArithC(..)
  , Sort(..)

  , cconv
  , runConv
  , pprintTerm
  ) where

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.Reader

import Data.List (intercalate, partition)

import qualified CPS as K
import CPS (TermK(..), FunDef(..), ContDef(..), ValueK(..), ArithK(..))

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
newtype Name = Name String
  deriving (Eq, Ord)

instance Show Name where
  show (Name x) = x

tmVar :: K.TmVar -> Name
tmVar (K.TmVar x) = Name x
-- tmVar (K.TmVar x) = (Name x, Value)

coVar :: K.CoVar -> Name
coVar (K.CoVar k) = Name k

fnName :: K.FnName -> Name
fnName (K.FnName f) = Name f

-- | 'Sort' is really a simplified form of type information.
-- Value = int | bool | t1 * t2 | t1 + t2 | ()
-- Closure = (t1, t2, ...) -> 0
-- Alloc = a : *
data Sort = Closure | Value | Alloc
  deriving (Eq, Ord)

instance Show Sort where
  show Closure = "closure"
  show Value = "value"
  show Alloc = "alloc_header"

sortOf :: K.TypeK -> Sort
sortOf (K.ContK _) = Closure
sortOf _ = Value

-- Closure conversion is bottom-up (to get flat closures) traversal that
-- replaces free variables with references to an environment parameter.
data TermC
  = LetValC (Name, Sort) ValueC TermC -- let x = v in e, allocation
  | LetFstC (Name, Sort) Name TermC -- let x = fst y in e, projection
  | LetSndC (Name, Sort) Name TermC
  | LetArithC Name ArithC TermC
  | LetIsZeroC Name Name TermC
  | LetFunC [FunClosureDef] TermC
  | LetContC [ContClosureDef] TermC
  -- Invoke a closure by providing a value for the only remaining argument.
  | JumpC Name Name -- k x
  | CallC Name Name Name -- f x k
  | HaltC Name
  | CaseC Name Name Name -- case x of k1 | k2

data ArithC
  = AddC Name Name
  | SubC Name Name
  | MulC Name Name

-- | @f {x+} y k = e@
-- Closures capture two sets of names: those from outer scopes, and those from
-- the same recursive bind group.
data FunClosureDef
  = FunClosureDef {
    funClosureName :: Name
  , funClosureFreeNames :: [(Name, Sort)]
  , funClosureRecNames :: [(Name, Sort)]
  , funClosureParam :: (Name, Sort)
  , funClosureCont :: (Name, Sort)
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
  , contClosureParam :: (Name, Sort)
  , contClosureBody :: TermC
  }

data ValueC
  = PairC Name Name
  | InlC Name
  | InrC Name
  | NilC
  | IntC Int


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


fieldsFor :: TermK -> FieldsFor
fieldsFor (LetFunK fs e) = foldMap fieldsForFunDef fs <> bindFields fs' (fieldsFor e)
  where fs' = funDefNames fs
fieldsFor (LetContK ks e) = foldMap fieldsForContDef ks <> bindFields ks' (fieldsFor e)
  where ks' = contDefNames ks
fieldsFor (HaltK x) = unitField (tmVar x)
fieldsFor (JumpK k x) = unitField (coVar k) <> unitField (tmVar x)
fieldsFor (CallK f x k) = unitField (fnName f) <> unitField (tmVar x) <> unitField (coVar k)
fieldsFor (CaseK x k1 k2) = unitField (tmVar x) <> unitField (coVar k1) <> unitField (coVar k2)
fieldsFor (LetFstK x t y e) = unitField (tmVar y) <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetSndK x t y e) = unitField (tmVar y) <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetValK x t v e) = fieldsForValue v <> bindFields [(tmVar x, sortOf t)] (fieldsFor e)
fieldsFor (LetArithK x op e) = fieldsForArith op <> bindFields [(tmVar x, Value)] (fieldsFor e)
fieldsFor (LetIsZeroK x y e) = unitField (tmVar y) <> bindFields [(tmVar x, Value)] (fieldsFor e)

fieldsForArith :: ArithK -> FieldsFor
fieldsForArith (AddK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForArith (SubK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForArith (MulK x y) = unitField (tmVar x) <> unitField (tmVar y)

fieldsForValue :: ValueK -> FieldsFor
fieldsForValue (IntValK _) = mempty
fieldsForValue NilK = mempty
fieldsForValue (PairK x y) = unitField (tmVar x) <> unitField (tmVar y)
fieldsForValue (InlK x) = unitField (tmVar x)
fieldsForValue (InrK y) = unitField (tmVar y)

fieldsForFunDef :: FunDef -> FieldsFor
fieldsForFunDef (FunDef _f x t k s e) =
  bindFields [(tmVar x, sortOf t), (coVar k, sortOf s)] (fieldsFor e)

fieldsForContDef :: ContDef -> FieldsFor
fieldsForContDef (ContDef _k x t e) =
  bindFields [(tmVar x, sortOf t)] (fieldsFor e)

-- | Split occurrences into free variables and recursive calls.
-- Return @(free, rec)@.
markRec :: Set Name -> [(Name, Sort)] -> ([(Name, Sort)], [(Name, Sort)])
markRec fs xs = partition (\ (x, _) -> if Set.member x fs then False else True) xs

funDefNames :: [FunDef] -> [(Name, Sort)]
funDefNames fs = [(fnName f, Closure) | FunDef f _ _ _ _ _ <- fs]

contDefNames :: [ContDef] -> [(Name, Sort)]
contDefNames ks = [(coVar k, Closure) | ContDef k _ _ _ <- ks]

newtype ConvM a = ConvM { runConvM :: Reader (Map Name Sort) a }

deriving newtype instance Functor ConvM
deriving newtype instance Applicative ConvM
deriving newtype instance Monad ConvM
deriving newtype instance MonadReader (Map Name Sort) ConvM

runConv :: ConvM a -> a
runConv = flip runReader Map.empty . runConvM

cconv :: TermK -> ConvM TermC
cconv (LetFunK fs e) = LetFunC <$> local extendGroup (traverse ann fs) <*> local extendGroup (cconv e)
  where
    fs' = Set.fromList (fst <$> funDefNames fs)
    extendGroup ctx = foldr (uncurry Map.insert) ctx (funDefNames fs)
    ann fun@(FunDef f x t k s e') = do
      ctx <- ask
      let extend ctx' = Map.insert (tmVar x) Value $ Map.insert (coVar k) Closure $ ctx'
      let fields = Set.toList $ runFieldsFor (fieldsForFunDef fun) (extend ctx)
      let (free, rec) = markRec fs' fields
      FunClosureDef (fnName f) free rec (tmVar x, sortOf t) (coVar k, sortOf s) <$> local extend (cconv e')
cconv (LetContK ks e) = LetContC <$> local extendGroup (traverse ann ks) <*> local extendGroup (cconv e)
  where
    ks' = Set.fromList (fst <$> contDefNames ks)
    extendGroup ctx = foldr (uncurry Map.insert) ctx (contDefNames ks)
    ann kont@(ContDef k x t e') = do
      ctx <- ask
      let extend ctx' = Map.insert (tmVar x) Value ctx'
      let fields = runFieldsFor (fieldsForContDef kont) (extend ctx)
      let (free, rec) = markRec ks' (Set.toList fields)
      ContClosureDef (coVar k) free rec (tmVar x, sortOf t) <$> local extend (cconv e')
cconv (HaltK x) = pure $ HaltC (tmVar x)
cconv (JumpK k x) = pure $ JumpC (coVar k) (tmVar x)
cconv (CallK f x k) = pure $ CallC (fnName f) (tmVar x) (coVar k)
cconv (CaseK x k1 k2) = pure $ CaseC (tmVar x) (coVar k1) (coVar k2)
cconv (LetFstK x t y e) = LetFstC (tmVar x, sortOf t) (tmVar y) <$> cconv e
cconv (LetSndK x t y e) = LetSndC (tmVar x, sortOf t) (tmVar y) <$> cconv e
cconv (LetIsZeroK x y e) = LetIsZeroC (tmVar x) (tmVar y) <$> cconv e
cconv (LetValK x t v e) = LetValC (tmVar x, sortOf t) (cconvValue v) <$> cconv e
cconv (LetArithK x op e) = LetArithC (tmVar x) (cconvArith op) <$> cconv e

cconvValue :: ValueK -> ValueC
cconvValue NilK = NilC
cconvValue (PairK x y) = PairC (tmVar x) (tmVar y)
cconvValue (IntValK i) = IntC i
cconvValue (InlK x) = InlC (tmVar x)
cconvValue (InrK y) = InrC (tmVar y)

cconvArith :: ArithK -> ArithC
cconvArith (AddK x y) = AddC (tmVar x) (tmVar y)
cconvArith (SubK x y) = SubC (tmVar x) (tmVar y)
cconvArith (MulK x y) = MulC (tmVar x) (tmVar y)

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
pprintTerm n (JumpC k x) = indent n $ show k ++ " " ++ show x ++ ";\n"
pprintTerm n (CallC f x k) = indent n $ show f ++ " " ++ show x ++ " " ++ show k ++ ";\n"
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
pprintTerm n (LetIsZeroC x y e) =
  indent n ("let " ++ show x ++ " = iszero " ++ show y ++ ";\n") ++ pprintTerm n e
pprintTerm n (CaseC x k1 k2) =
  indent n $ "case " ++ show x ++ " of " ++ show k1 ++ " | " ++ show k2 ++ ";\n"
pprintTerm n (LetArithC x op e) =
  indent n ("let " ++ show x ++ " = " ++ pprintArith op ++ ";\n") ++ pprintTerm n e

pprintPlace :: (Name, Sort) -> String
pprintPlace (x, s) = show s ++ " " ++ show x

pprintValue :: ValueC -> String
pprintValue NilC = "()"
pprintValue (PairC x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
pprintValue (IntC i) = show i
pprintValue (InlC x) = "inl " ++ show x
pprintValue (InrC y) = "inr " ++ show y

pprintArith :: ArithC -> String
pprintArith (AddC x y) = show x ++ " + " ++ show y
pprintArith (SubC x y) = show x ++ " - " ++ show y
pprintArith (MulC x y) = show x ++ " * " ++ show y

pprintClosureDef :: Int -> FunClosureDef -> String
pprintClosureDef n (FunClosureDef f free rec x k e) =
  indent n env ++ indent n (show f ++ " " ++ pprintPlace x ++ " " ++ pprintPlace k ++ " =\n") ++ pprintTerm (n+2) e
  where
    env = "{" ++ intercalate ", " vars ++ "}\n"
    vars = map (\ (v, s) -> show s ++ " " ++ show v) (free ++ rec)

pprintContClosureDef :: Int -> ContClosureDef -> String
pprintContClosureDef n (ContClosureDef k free rec x e) =
  indent n env ++ indent n (show k ++ " " ++ pprintPlace x ++ " =\n") ++ pprintTerm (n+2) e
  where
    env = "{" ++ intercalate ", " vars ++ "}\n"
    vars = map (\ (v, s) -> show s ++ " " ++ show v) (free ++ rec)
