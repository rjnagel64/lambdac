
-- | Check that a CPS'ed program is well-typed.
module CPS.TypeCheck (checkProgram, TypeError(..)) where

import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Map as Map
import Data.Map (Map)

import Data.Foldable (for_, traverse_)

import CPS.IR

import Prelude hiding (cos)


data TypeError
  = TmNotInScope TmVar
  | CoNotInScope CoVar
  | TyNotInScope TyVar
  | TypeMismatch TypeK TypeK
  | CoTypeMismatch CoTypeK CoTypeK
  | KindMismatch KindK KindK
  | BadCaseAnalysis TmVar TypeK
  | ArityMismatch
  | BadValue ValueK TypeK
  | BadProjection TypeK
  | CannotCall TmVar TypeK
  | CannotInst TmVar TypeK

instance Show TypeError where
  show (TmNotInScope x) = "term variable " ++ show x ++ " not in scope"
  show (CoNotInScope k) = "continuation variable " ++ show k ++ " not in scope"
  show (TyNotInScope aa) = "type variable " ++ show aa ++ " not in scope"
  show (TypeMismatch expected actual) = unlines
    [ "type mismatch:"
    , "expected type: " ++ pprintType expected
    , "actual type:   " ++ pprintType actual
    ]
  show (CoTypeMismatch expected actual) = unlines
    [ "type mismatch:"
    , "expected type: " ++ pprintCoType expected
    , "actual type:   " ++ pprintCoType actual
    ]
  show (KindMismatch expected actual) = unlines
    [ "kind mismatch:"
    , "expected kind: " ++ pprintKind expected
    , "actual kind:   " ++ pprintKind actual
    ]
  show (BadCaseAnalysis x s) = "cannot analyze cases for " ++ show x ++ " of type " ++ pprintType s
  show ArityMismatch = "incorrect arity"
  show (BadValue v t) = "value " ++ pprintValue v ++ " does not have expected type " ++ pprintType t
  show (BadProjection t) = "cannot project a field from value of type " ++ pprintType t
  show (CannotCall f t) = 
    "variable " ++ show f ++ " is applied to arguments but its type is not a function: "
    ++ pprintType t
  show (CannotInst f t) = 
    "variable " ++ show f ++ " is applied to type arguments but its type is not a forall: "
    ++ pprintType t

newtype M a = M { getM :: ReaderT Context (Except TypeError) a }

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader Context M
deriving newtype instance MonadError TypeError M

runM :: M a -> Either TypeError a
runM = runExcept . flip runReaderT emptyContext . getM

data Context
  = Context {
    tmContext :: Map TmVar TypeK
  , coContext :: Map CoVar CoTypeK
  , tyContext :: Map TyVar KindK
  }

emptyContext :: Context
emptyContext = Context Map.empty Map.empty Map.empty

withTmVars :: [(TmVar, TypeK)] -> M a -> M a
withTmVars [] m = m
withTmVars ((x, t):xs) m = checkType t StarK *> local extend (withTmVars xs m)
  where extend (Context tms cos tys) = Context (Map.insert x t tms) cos tys

withCoVars :: [(CoVar, CoTypeK)] -> M a -> M a
withCoVars [] m = m
withCoVars ((k, s):ks) m = checkCoType s StarK *> local extend (withCoVars ks m)
  where extend (Context tms cos tys) = Context tms (Map.insert k s cos) tys

withTyVars :: [(TyVar, KindK)] -> M a -> M a
withTyVars [] m = m
withTyVars ((aa, kk) : aas) m = checkKind kk *> local extend (withTyVars aas m)
  where extend (Context tms cos tys) = Context tms cos (Map.insert aa kk tys)

lookupTmVar :: TmVar -> M TypeK
lookupTmVar x = asks tmContext >>= maybe err pure . Map.lookup x
  where err = throwError (TmNotInScope x)

lookupCoVar :: CoVar -> M CoTypeK
lookupCoVar x = asks coContext >>= maybe err pure . Map.lookup x
  where err = throwError (CoNotInScope x)

lookupTyVar :: TyVar -> M KindK
lookupTyVar x = asks tyContext >>= maybe err pure . Map.lookup x
  where err = throwError (TyNotInScope x)

equalTypes :: TypeK -> TypeK -> M ()
equalTypes expected actual =
  unless (eqTypeK expected actual) $ throwError (TypeMismatch expected actual)

equalCoTypes :: CoTypeK -> CoTypeK -> M ()
equalCoTypes expected actual =
  unless (eqCoTypeK expected actual) $ throwError (CoTypeMismatch expected actual)

equalKinds :: KindK -> KindK -> M ()
equalKinds expected actual =
  unless (expected == actual) $ throwError (KindMismatch expected actual)

instantiate :: [(TyVar, KindK)] -> [TypeK] -> [CoTypeK] -> M [CoTypeK]
instantiate aas ts ss = do
  sub <- makeSubst <$> zipExact aas ts
  pure (map (substCoTypeK sub) ss)
  where
    zipExact [] [] = pure []
    zipExact ((aa, kk):aas') (t:ts') = do
      checkType t kk
      rest <- zipExact aas' ts'
      pure ((aa, t) : rest)
    zipExact _ _ = throwError ArityMismatch


checkProgram :: TermK () -> Either TypeError ()
checkProgram e = runM (check e)


check :: TermK a -> M ()
check (HaltK x) = do
  _ <- lookupTmVar x
  pure ()
check (JumpK k xs) = do
  ContK ss <- lookupCoVar k
  checkTmArgs xs ss
check (CallK f xs ks) = do
  (ts, ss) <- lookupTmVar f >>= \case
    FunK ts ss -> pure (ts, ss)
    t -> throwError (CannotCall f t)
  checkTmArgs xs ts
  checkCoArgs ks ss
check (InstK f ts ks) = do
  (aas, ss) <- lookupTmVar f >>= \case
    AllK aas ss -> pure (aas, ss)
    t -> throwError (CannotInst f t)
  ss' <- instantiate aas ts ss
  checkCoArgs ks ss'
check (CaseK x s ks) = case (s, ks) of
  (BoolK, [k1, k2]) ->
    checkCoVar k1 (ContK []) *> checkCoVar k2 (ContK [])
  (SumK t1 t2, [k1, k2]) ->
    checkCoVar k1 (ContK [t1]) *> checkCoVar k2 (ContK [t2])
  (ListK t, [k1, k2]) ->
    checkCoVar k1 (ContK []) *> checkCoVar k2 (ContK [t, ListK t])
  (_, _) -> throwError (BadCaseAnalysis x s)
check (LetContK ks e) = do
  let defs = map (\k -> (contDefName k, contDefType k)) ks
  withCoVars defs $ do
    for_ ks $ \ (ContDef _ _ xs e') -> do
      withTmVars xs $ check e'
    check e
check (LetFunAbsK fs e) = do
  let defs = map (\f -> (funDefName f, funDefType f)) fs
  withTmVars defs $ do
    for_ fs $ \case
      FunDef _ _ xs ks e' ->
        withTmVars xs $ withCoVars ks $ check e'
      AbsDef _ _ as ks e' ->
        withTyVars as $ withCoVars ks $ check e'
    check e
check (LetValK x t v e) = do
  checkValue v t
  withTmVars [(x, t)] $ check e
check (LetArithK z op e) = do
  checkArith op
  withTmVars [(z, IntK)] $ check e
check (LetCompareK z op e) = do
  checkCompare op
  withTmVars [(z, BoolK)] $ check e
check (LetFstK x t y e) = do
  lookupTmVar y >>= \case
    ProdK t' _s -> equalTypes t t'
    t' -> throwError (BadProjection t')
  withTmVars [(x, t)] $ check e
check (LetSndK x s y e) = do
  lookupTmVar y >>= \case
    ProdK _t s' -> equalTypes s s'
    t' -> throwError (BadProjection t')
  withTmVars [(x, s)] $ check e
check (LetConcatK x y z e) = do
  checkTmVar y StringK
  checkTmVar z StringK
  withTmVars [(x, StringK)] $ check e

checkArith :: ArithK -> M ()
checkArith (AddK x y) = checkIntBinOp x y
checkArith (SubK x y) = checkIntBinOp x y
checkArith (MulK x y) = checkIntBinOp x y
checkArith (NegK x) = checkTmVar x IntK

checkCompare :: CmpK -> M ()
checkCompare (CmpEqK x y) = checkIntBinOp x y
checkCompare (CmpNeK x y) = checkIntBinOp x y
checkCompare (CmpLtK x y) = checkIntBinOp x y
checkCompare (CmpLeK x y) = checkIntBinOp x y
checkCompare (CmpGtK x y) = checkIntBinOp x y
checkCompare (CmpGeK x y) = checkIntBinOp x y

checkIntBinOp :: TmVar -> TmVar -> M ()
checkIntBinOp x y = do
  checkTmVar x IntK
  checkTmVar y IntK

checkValue :: ValueK -> TypeK -> M ()
checkValue NilK UnitK = pure ()
checkValue (PairK x y) (ProdK t s) = do
  checkTmVar x t
  checkTmVar y s
checkValue (InlK x) (SumK t _s) = do
  checkTmVar x t
checkValue (InrK y) (SumK _t s) = do
  checkTmVar y s
checkValue (IntValK _) IntK = pure ()
checkValue (BoolValK _) BoolK = pure ()
checkValue (StringValK _) StringK = pure ()
checkValue EmptyK (ListK _) = pure ()
checkValue (ConsK x xs) (ListK t) = checkTmVar x t *> checkTmVar xs (ListK t)
checkValue v t = throwError (BadValue v t)

checkTmVar :: TmVar -> TypeK -> M ()
checkTmVar x t = do
  t' <- lookupTmVar x
  equalTypes t t'

checkCoVar :: CoVar -> CoTypeK -> M ()
checkCoVar x t = do
  t' <- lookupCoVar x
  equalCoTypes t t'

checkTmArgs :: [TmVar] -> [TypeK] -> M ()
checkTmArgs [] [] = pure ()
checkTmArgs (x:xs) (s:ss) = checkTmVar x s *> checkTmArgs xs ss
checkTmArgs _ _ = throwError ArityMismatch

checkCoArgs :: [CoVar] -> [CoTypeK] -> M ()
checkCoArgs [] [] = pure ()
checkCoArgs (k:ks) (s:ss) = checkCoVar k s *> checkCoArgs ks ss
checkCoArgs _ _ = throwError ArityMismatch


-- | Check that a type has the given kind.
checkType :: TypeK -> KindK -> M ()
checkType (TyVarOccK aa) kk = do
  kk' <- lookupTyVar aa
  equalKinds kk kk'
checkType (AllK aas ss) StarK = withTyVars aas (traverse_ (\s -> checkCoType s StarK) ss)
checkType (FunK ts ss) StarK =
  traverse_ (\t -> checkType t StarK) ts *>
  traverse_ (\s -> checkCoType s StarK) ss
checkType (ProdK t s) StarK = checkType t StarK *> checkType s StarK
checkType (SumK t s) StarK = checkType t StarK *> checkType s StarK
checkType (ListK t) StarK = checkType t StarK
checkType UnitK StarK = pure ()
checkType IntK StarK = pure ()
checkType BoolK StarK = pure ()
checkType StringK StarK = pure ()

-- | Check that a co-type has the given kind.
checkCoType :: CoTypeK -> KindK -> M ()
checkCoType (ContK ts) StarK = traverse_ (\t -> checkType t StarK) ts

-- | Check that a kind is well-formed.
checkKind :: KindK -> M ()
checkKind StarK = pure ()
