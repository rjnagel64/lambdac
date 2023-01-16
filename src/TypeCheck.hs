
module TypeCheck
    ( checkProgram
    ) where

import Source

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (traverse_, for_)

import Control.Monad.Except
import Control.Monad.Reader


data TCError
  = NotInScope TmVar
  | TyNotInScope TyVar
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
  show (TyNotInScope aa) = "type variable not in scope: " ++ show aa
  show (CannotApply t) = "value of type " ++ pprintType 0 t ++ " cannot have a value applied to it"
  show (CannotInstantiate t) = "value of type " ++ pprintType 0 t ++ " cannot have a type applied to it"
  show (CannotProject t) = "cannot project field from value of type " ++ pprintType 0 t
  show (InvalidLetRec f) = "invalid definition " ++ show f ++ " in a letrec binding"

newtype TC a = TC { runTC :: ReaderT (Map TmVar Type, Map TyVar Kind) (Except TCError) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader (Map TmVar Type, Map TyVar Kind) TC
deriving newtype instance MonadError TCError TC

withVars :: [(TmVar, Type)] -> TC a -> TC a
withVars xs m = do
  traverse_ (wfType . snd) xs
  local f m
  where
    f (tms, tys) = (foldr (uncurry Map.insert) tms xs, tys)

withTyVars :: [(TyVar, Kind)] -> TC a -> TC a
withTyVars aas = local f
  where
    f (tms, tys) = (tms, foldr (uncurry Map.insert) tys aas)

infer :: Term -> TC Type
infer (TmVarOcc x) = do
  (env, _) <- ask
  case Map.lookup x env of
    Just t -> pure t
    Nothing -> throwError (NotInScope x)
infer (TmLet x t e1 e2) = do
  check e1 t
  withVars [(x, t)] $ infer e2

infer (TmLetRec bs e) = do
  for_ bs $ \ (x, _, rhs) -> case rhs of
    TmLam _ _ _ -> pure ()
    TmTLam _ _ _ -> pure ()
    _ -> throwError (InvalidLetRec x)
  let binds = [(x, t) | (x, t, _) <- bs]
  withVars binds $ traverse_ (\ (_, t, e') -> check e' t) bs
  withVars binds $ infer e
infer (TmRecFun fs e) = do
  let binds = [(f, TyArr t s) | TmFun f _ t s _ <- fs]
  withVars binds $ traverse_ checkFun fs
  withVars binds $ infer e

infer (TmBool _) = pure TyBool
infer (TmInt _) = pure TyInt
infer (TmString _) = pure TyString

infer (TmLam x t e) = do
  t' <- withVars [(x, t)] $ infer e
  pure (TyArr t t')
infer (TmApp e1 e2) = do
  infer e1 >>= \case
    TyArr t1 t2 -> do
      check e2 t1
      pure t2
    t -> throwError (CannotApply t)

infer (TmTLam aa ki e) = do
  t <- withTyVars [(aa, ki)] $ infer e
  pure (TyAll aa ki t)
infer (TmTApp e t) = do
  infer e >>= \case
    TyAll aa KiStar t' -> do
      wfType t
      pure (substType (singleSubst aa t) t')
    t' -> throwError (CannotInstantiate t')

infer (TmIf c a t f) = do
  check c TyBool
  check t a
  check f a
  pure a

infer (TmInl a b e) = do
  check e a
  pure (TySum a b)
infer (TmInr a b e) = do
  check e b
  pure (TySum a b)
infer (TmCase e c (xl, tl, el) (xr, tr, er)) = do
  check e (TySum tl tr)
  withVars [(xl, tl)] $ check el c
  withVars [(xr, tr)] $ check er c
  pure c

infer (TmEmpty t) = pure (TyList t)
infer (TmCons t e1 e2) = do
  check e1 t
  check e2 (TyList t)
  pure (TyList t)
infer (TmCaseList e s enil ((xhead, thead), (xtail, ttail), econs)) = do
  check e (TyList thead)
  check enil s
  withVars [(xhead, thead), (xtail, ttail)] $ check econs s
  pure s

infer TmNil = pure TyUnit
infer (TmPair e1 e2) = TyProd <$> infer e1 <*> infer e2
infer (TmFst e) = do
  infer e >>= \case
    TyProd t1 _t2 -> pure t1
    t -> throwError (CannotProject t)
infer (TmSnd e) = do
  infer e >>= \case
    TyProd _t1 t2 -> pure t2
    t -> throwError (CannotProject t)

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
infer (TmConcat e1 e2) = do
  check e1 TyString
  check e2 TyString
  pure TyString

check :: Term -> Type -> TC ()
check e t = do
  t' <- infer e
  when (t /= t') $ throwError (TypeMismatch t t')
  pure ()

checkFun :: TmFun -> TC ()
checkFun (TmFun _f x t s e) = do
  withVars [(x, t)] $ check e s
checkFun (TmTFun _f aa ki t e) = do
  withTyVars [(aa, ki)] $ check e t

-- | 'wfType' asserts that its argument is a well-formed type of kind @*@.
-- I will probably need a new function when I add type-level application.
wfType :: Type -> TC ()
wfType (TyAll aa ki t) = withTyVars [(aa, ki)] $ wfType t
wfType (TyVarOcc aa) = do
  ctx <- asks snd
  case Map.lookup aa ctx of
    Nothing -> throwError (TyNotInScope aa)
    Just KiStar -> pure ()
wfType TyUnit = pure ()
wfType TyInt = pure ()
wfType TyString = pure ()
wfType TyBool = pure ()
wfType (TyList t) = wfType t
wfType (TySum t s) = wfType t *> wfType s
wfType (TyProd t s) = wfType t *> wfType s
wfType (TyArr t s) = wfType t *> wfType s

checkProgram :: Program -> Either TCError ()
checkProgram (Program ds e) = runExcept . flip runReaderT (Map.empty, Map.empty) $ runTC $ do
  _ <- infer e
  pure ()

