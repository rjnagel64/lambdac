
module TypeCheck
    ( checkProgram
    ) where

import Source

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (traverse_)

import Control.Monad.Except
import Control.Monad.Reader


data TCError
  = NotInScope TmVar
  | TypeMismatch Type Type -- expected, actual
  | CannotProject Type
  | CannotApply Type

instance Show TCError where
  show (TypeMismatch expected actual) = unlines
    ["type mismatch:"
    ,"expected: " ++ pprintType 0 expected
    ,"actual:   " ++ pprintType 0 actual
    ]
  show (NotInScope x) = "variable not in scope: " ++ show x
  show (CannotApply t) = "cannot apply argument to value of type " ++ pprintType 0 t
  show (CannotProject t) = "cannot project field from value of type " ++ pprintType 0 t

-- something something showsPrec
pprintType :: Int -> Type -> String
pprintType p TyUnit = "unit"
pprintType p TyBool = "bool"
pprintType p TyInt = "int"
-- infixr 4 ->
pprintType p (TyArr t1 t2) = parensIf (p > 4) $ pprintType 5 t1 ++ " -> " ++ pprintType 4 t2
-- infix 5 *
pprintType p (TyProd t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " * " ++ pprintType 6 t2
-- infix 5 +
pprintType p (TySum t1 t2) = parensIf (p > 5) $ pprintType 6 t1 ++ " + " ++ pprintType 6 t2

parensIf :: Bool -> String -> String
parensIf True x = "(" ++ x ++ ")"
parensIf False x = x


newtype TC a = TC { runTC :: ReaderT (Map TmVar Type) (Except TCError) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader (Map TmVar Type) TC
deriving newtype instance MonadError TCError TC

withVars :: [(TmVar, Type)] -> TC a -> TC a
withVars xs = local f
  where
    f ctx = foldr (uncurry Map.insert) ctx xs

infer :: Term -> TC Type
infer (TmVarOcc x) = do
  env <- ask
  case Map.lookup x env of
    Just t -> pure t
    Nothing -> throwError (NotInScope x)
infer TmNil = pure TyUnit
infer (TmBool _) = pure TyBool
infer (TmInt _) = pure TyInt
infer (TmPair e1 e2) = TyProd <$> infer e1 <*> infer e2
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
checkProgram e = runExcept . flip runReaderT Map.empty $ runTC $ infer e *> pure ()

-- TODO: What if instead of bool, I returned a datastructure pointing out the
-- path to the first(?) (or all) discrepancy? (Context as to why the equality failed)
-- TODO: Support polymorphic types here.
eqType :: Type -> Type -> Bool
eqType TyUnit TyUnit = True
eqType TyUnit _ = False
eqType TyBool TyBool = True
eqType TyBool _ = False
eqType TyInt TyInt = True
eqType TyInt _ = False
eqType (TyProd t1 t2) (TyProd t3 t4) = eqType t1 t3 && eqType t2 t4
eqType (TyProd _ _) _ = False
eqType (TySum t1 t2) (TySum t3 t4) = eqType t1 t3 && eqType t2 t4
eqType (TySum _ _) _ = False
eqType (TyArr t1 t2) (TyArr t3 t4) = eqType t1 t3 && eqType t2 t4
eqType (TyArr _ _) _ = False
