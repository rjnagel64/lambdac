
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
eqType' fw bw (TyList a) (TyList b) = eqType' fw bw a b
eqType' _ _ (TyList _) _ = False

-- | Perform a substitution, @subst aa t t' === t'[aa := t]@.
subst :: TyVar -> Type -> Type -> Type
subst aa t (TyVarOcc bb) = if aa == bb then t else TyVarOcc bb
subst aa t (TyAll bb t') =
  if aa == bb then TyAll bb t' else TyAll bb' (subst aa t (subst bb (TyVarOcc bb') t'))
  where
    vs = ftv t' <> ftv t
    bb' = let TyVar x = bb in go x
    go x = if Set.member (TyVar x) vs then go (x ++ "'") else TyVar x
subst aa t (TyList t') = TyList (subst aa t t')
subst aa t (TySum t1 t2) = TySum (subst aa t t1) (subst aa t t2)
subst aa t (TyProd t1 t2) = TyProd (subst aa t t1) (subst aa t t2)
subst aa t (TyArr t1 t2) = TyArr (subst aa t t1) (subst aa t t2)
subst _ _ TyUnit = TyUnit
subst _ _ TyBool = TyBool
subst _ _ TyInt = TyInt

ftv :: Type -> Set TyVar
ftv (TyVarOcc aa) = Set.singleton aa
ftv (TyAll bb t) = Set.delete bb (ftv t)
ftv (TySum t1 t2) = ftv t1 <> ftv t2
ftv (TyProd t1 t2) = ftv t1 <> ftv t2
ftv (TyArr t1 t2) = ftv t1 <> ftv t2
ftv TyUnit = Set.empty
ftv TyBool = Set.empty
ftv TyInt = Set.empty
ftv (TyList t) = ftv t
