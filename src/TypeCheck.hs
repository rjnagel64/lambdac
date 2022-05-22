
module TypeCheck
    ( checkProgram
    ) where

import Source

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (traverse_)

import Control.Monad.Except
import Control.Monad.Reader

-- TODO: This is kind of redundant with CPS. Once I iron out the bugs in CPS,
-- this will be obsolete.


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
  let binds = [(x, t) | (x, t, _) <- bs]
  withVars binds $ traverse_ (\ (_, t, e') -> check e' t) bs
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

eqType :: Type -> Type -> Bool
eqType = eqType' Map.empty Map.empty

eqType' :: Map TyVar TyVar -> Map TyVar TyVar -> Type -> Type -> Bool
eqType' fw bw (TyVarOcc x) (TyVarOcc y) = case (Map.lookup x fw, Map.lookup y bw) of
  -- Both bound: check that bijection holds
  (Just y', Just x') -> y' == y && x' == x
  -- Both free: require exact equality
  (Nothing, Nothing) -> x == y
  -- Cannot be equal if one free but the other is bound
  _ -> False
eqType' _ _ (TyVarOcc _) _ = False
eqType' _ _ TyUnit TyUnit = True
eqType' _ _ TyUnit _ = False
eqType' _ _ TyBool TyBool = True
eqType' _ _ TyBool _ = False
eqType' _ _ TyInt TyInt = True
eqType' _ _ TyInt _ = False
eqType' fw bw (TyProd t1 t2) (TyProd t3 t4) = eqType' fw bw t1 t3 && eqType' fw bw t2 t4
eqType' _ _ (TyProd _ _) _ = False
eqType' fw bw (TySum t1 t2) (TySum t3 t4) = eqType' fw bw t1 t3 && eqType' fw bw t2 t4
eqType' _ _ (TySum _ _) _ = False
eqType' fw bw (TyArr arg1 ret1) (TyArr arg2 ret2) =
  eqType' fw bw arg1 arg2 && eqType' fw bw ret1 ret2
eqType' _ _ (TyArr _ _) _ = False
eqType' fw bw (TyAll x t) (TyAll y s) = eqType' (Map.insert x y fw) (Map.insert y x bw) t s
eqType' _ _ (TyAll _ _) _ = False

