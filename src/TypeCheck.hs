
module TypeCheck
    ( checkProgram
    ) where

import Source

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Foldable (traverse_, for_)

import Control.Monad.Except
import Control.Monad.Reader


data TCError
  = NotInScope TmVar
  | TypeMismatch Type Type -- expected, actual
  | CannotProject Type
  | CannotApply Type
  | CannotInstantiate Type
  | InvalidLetRec TmVar

instance Show TCError where
  show (TypeMismatch expected actual) = unlines
    ["type mismatch:"
    ,"expected: " ++ pprintType 0 expected
    ,"actual:   " ++ pprintType 0 actual
    ]
  show (NotInScope x) = "variable not in scope: " ++ show x
  show (CannotApply t) = "value of type " ++ pprintType 0 t ++ " cannot have a value applied to it"
  show (CannotInstantiate t) = "value of type " ++ pprintType 0 t ++ " cannot have a type applied to it"
  show (CannotProject t) = "cannot project field from value of type " ++ pprintType 0 t
  show (InvalidLetRec f) = "invalid definition " ++ show f ++ " in a letrec binding"

newtype TC a = TC { runTC :: ReaderT (Map TmVar Type, Set TyVar) (Except TCError) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader (Map TmVar Type, Set TyVar) TC
deriving newtype instance MonadError TCError TC

withVars :: [(TmVar, Type)] -> TC a -> TC a
withVars xs = local f
  where
    f (tms, tys) = (foldr (uncurry Map.insert) tms xs, tys)

withTyVars :: [TyVar] -> TC a -> TC a
withTyVars aas = local f
  where
    f (tms, tys) = (tms, foldr Set.insert tys aas)

infer :: Term -> TC Type
infer (TmVarOcc x) = do
  (env, _) <- ask
  case Map.lookup x env of
    Just t -> pure t
    Nothing -> throwError (NotInScope x)
infer TmNil = pure TyUnit
infer (TmEmpty t) = pure (TyList t)
infer (TmBool _) = pure TyBool
infer (TmInt _) = pure TyInt
infer (TmPair e1 e2) = TyProd <$> infer e1 <*> infer e2
infer (TmCons e1 e2) = do
  thead <- infer e1
  check e2 (TyList thead)
  pure (TyList thead)
infer (TmIf c a t f) = do
  check c TyBool
  check t a
  check f a
  pure a
infer (TmCase e c (xl, tl, el) (xr, tr, er)) = do
  check e (TySum tl tr)
  withVars [(xl, tl)] $ check el c
  withVars [(xr, tr)] $ check er c
  pure c
infer (TmCaseList e s enil ((xhead, thead), (xtail, ttail), econs)) = do
  check e (TyList thead)
  check enil s
  withVars [(xhead, thead), (xtail, ttail)] $ check econs s
  pure s
infer (TmFst e) = do
  infer e >>= \case
    TyProd t1 _t2 -> pure t1
    t -> throwError (CannotProject t)
infer (TmSnd e) = do
  infer e >>= \case
    TyProd _t1 t2 -> pure t2
    t -> throwError (CannotProject t)
infer (TmInl a b e) = do
  check e a
  pure (TySum a b)
infer (TmInr a b e) = do
  check e b
  pure (TySum a b)
infer (TmApp e1 e2) = do
  infer e1 >>= \case
    TyArr t1 t2 -> do
      check e2 t1
      pure t2
    t -> throwError (CannotApply t)
infer (TmArith e1 _ e2) = do
  check e1 TyInt
  check e2 TyInt
  pure TyInt
infer (TmNegate e) = do
  check e TyInt
  pure TyInt
infer (TmCmp e1 _ e2) = do
  check e1 TyInt
  check e2 TyInt
  pure TyBool
infer (TmLet x t e1 e2) = do
  check e1 t
  withVars [(x, t)] $ infer e2
infer (TmLam x t e) = do
  t' <- withVars [(x, t)] $ infer e
  pure (TyArr t t')
infer (TmRecFun fs e) = do
  let binds = [(f, TyArr t s) | TmFun f _ t s _ <- fs]
  withVars binds $ traverse_ checkFun fs
  withVars binds $ infer e
infer (TmLetRec bs e) = do
  for_ bs $ \ (x, _, rhs) -> case rhs of
    TmLam _ _ _ -> pure ()
    _ -> throwError (InvalidLetRec x)
  let binds = [(x, t) | (x, t, _) <- bs]
  withVars binds $ traverse_ (\ (_, t, e') -> check e' t) bs
  withVars binds $ infer e
infer (TmTLam aa e) = do
  t <- withTyVars [aa] $ infer e
  pure (TyAll aa t)
infer (TmTApp e t) = do
  infer e >>= \case
    TyAll aa t' -> pure (subst aa t t')
    t' -> throwError (CannotInstantiate t')

check :: Term -> Type -> TC ()
check e t = do
  t' <- infer e
  when (not (eqType t t')) $ throwError (TypeMismatch t t')
  pure ()

checkFun :: TmFun -> TC ()
checkFun (TmFun _f x t s e) = do
  withVars [(x, t)] $ check e s
  pure ()


checkProgram :: Term -> Either TCError ()
checkProgram e = runExcept . flip runReaderT (Map.empty, Set.empty) $ runTC $ infer e *> pure ()

