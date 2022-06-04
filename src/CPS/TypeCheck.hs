
-- | Check that a CPS'ed program is well-typed.
module CPS.TypeCheck (check, runM) where

import Control.Monad.Except
import Control.Monad.Reader

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (for_)

import CPS

import Prelude hiding (cos)


data Context = Context { tmContext :: Map TmVar TypeK, coContext :: Map CoVar CoTypeK }

emptyContext :: Context
emptyContext = Context Map.empty Map.empty

data TypeError
  = TmNotInScope TmVar
  | CoNotInScope CoVar
  | TypeMismatch TypeK TypeK
  | CoTypeMismatch CoTypeK CoTypeK
  | BadCaseAnalysis TmVar TypeK
  | ArityMismatch
  | BadValue ValueK TypeK
  | BadProjection TypeK
  | CannotCall TmVar TypeK

newtype M a = M { getM :: ReaderT Context (Except TypeError) a }

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader Context M
deriving newtype instance MonadError TypeError M

runM :: M a -> Either TypeError a
runM = runExcept . flip runReaderT emptyContext . getM

withTmVars :: [(TmVar, TypeK)] -> M a -> M a
withTmVars xs = local extend
  where
    extend (Context tms cos) = Context (foldr (uncurry Map.insert) tms xs) cos

withCoVars :: [(CoVar, CoTypeK)] -> M a -> M a
withCoVars ks = local extend
  where
    extend (Context tms cos) = Context tms (foldr (uncurry Map.insert) cos ks)

check :: TermK a -> M ()
check (LetArithK z op e) = do
  checkArith op
  withTmVars [(z, IntK)] $ check e
check (LetCompareK z op e) = do
  checkCompare op
  withTmVars [(z, BoolK)] $ check e
check (LetNegateK x y e) = do
  checkTmVar y IntK
  withTmVars [(x, IntK)] $ check e
check (LetFstK x t y e) = do
  lookupTmVar y >>= \case
    ProdK t' _s -> when (not (eqTypeK t t')) $ throwError (TypeMismatch t t')
    t' -> throwError (BadProjection t')
  withTmVars [(x, t)] $ check e
check (LetSndK x s y e) = do
  lookupTmVar y >>= \case
    ProdK _t s' -> when (not (eqTypeK s s')) $ throwError (TypeMismatch s s')
    t' -> throwError (BadProjection t')
  withTmVars [(x, s)] $ check e
check (LetValK x t v e) = do
  checkValue v t
  withTmVars [(x, t)] $ check e
check (LetContK ks e) = do
  let defs = [(k, ContK (map snd xs)) | ContDef _ k xs _ <- ks]
  withCoVars defs $ do
    for_ ks $ \ (ContDef _ _ xs e') -> do
      withTmVars xs $ check e'
    check e
check (LetFunK fs e) = do
  let defs = [(f, FunK (map snd xs) (map snd ks)) | FunDef _ f xs ks _ <- fs]
  withTmVars defs $ do
    for_ fs $ \ (FunDef _ _ xs ks e') -> do
      withTmVars xs $ withCoVars ks $ check e'
    check e
check (HaltK _) = pure ()
check (JumpK k xs) = do
  ContK ss <- lookupCoVar k
  checkTmArgs xs ss
check (CallK f xs ks) = do
  (ts, ss) <- lookupTmVar f >>= \case
    FunK ts ss -> pure (ts, ss)
    t -> throwError (CannotCall f t)
  checkTmArgs xs ts
  checkCoArgs ks ss
check (CaseK x s ks) = case (s, ks) of
  (BoolK, [k1, k2]) ->
    checkCoVar k1 (ContK []) *> checkCoVar k2 (ContK [])
  (SumK t1 t2, [k1, k2]) ->
    checkCoVar k1 (ContK [t1]) *> checkCoVar k2 (ContK [t2])
  (ListK t, [k1, k2]) ->
    checkCoVar k1 (ContK []) *> checkCoVar k2 (ContK [t, ListK t])
  (_, _) -> throwError (BadCaseAnalysis x s)

checkArith :: ArithK -> M ()
checkArith (AddK x y) = checkIntBinOp x y
checkArith (SubK x y) = checkIntBinOp x y
checkArith (MulK x y) = checkIntBinOp x y

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
checkValue EmptyK (ListK _) = pure ()
checkValue (ConsK x xs) (ListK t) = checkTmVar x t *> checkTmVar xs (ListK t)
checkValue v t = throwError (BadValue v t)

checkTmVar :: TmVar -> TypeK -> M ()
checkTmVar x t = do
  t' <- lookupTmVar x
  when (not (eqTypeK t t')) $
    throwError $ TypeMismatch t t'

checkCoVar :: CoVar -> CoTypeK -> M ()
checkCoVar x t = do
  t' <- lookupCoVar x
  when (not (eqCoTypeK t t')) $
    throwError $ CoTypeMismatch t t'

checkTmArgs :: [TmVar] -> [TypeK] -> M ()
checkTmArgs [] [] = pure ()
checkTmArgs (x:xs) (s:ss) = checkTmVar x s *> checkTmArgs xs ss
checkTmArgs _ _ = throwError ArityMismatch

checkCoArgs :: [CoVar] -> [CoTypeK] -> M ()
checkCoArgs [] [] = pure ()
checkCoArgs (k:ks) (s:ss) = checkCoVar k s *> checkCoArgs ks ss
checkCoArgs _ _ = throwError ArityMismatch


lookupTmVar :: TmVar -> M TypeK
lookupTmVar x = asks tmContext >>= maybe err pure . Map.lookup x
  where err = throwError (TmNotInScope x)

lookupCoVar :: CoVar -> M CoTypeK
lookupCoVar x = asks coContext >>= pure . Map.lookup x >>= \case
  Nothing -> throwError (CoNotInScope x)
  Just s -> pure s
