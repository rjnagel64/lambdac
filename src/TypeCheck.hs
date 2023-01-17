
module TypeCheck
    ( checkProgram
    ) where

import Source

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Foldable (traverse_, for_)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State


data TCError
  = NotInScope TmVar
  | CtorNotInScope Ctor
  | TyNotInScope TyVar
  | TyConNotInScope TyCon
  | TypeMismatch Type Type -- expected, actual
  | KindMismatch Kind Kind -- expected, actual
  | CannotProject Type
  | CannotApply Type
  | CannotTyApp Type
  | CannotInstantiate Type
  | InvalidLetRec TmVar

instance Show TCError where
  show (TypeMismatch expected actual) = unlines
    ["type mismatch:"
    ,"expected: " ++ pprintType 0 expected
    ,"actual:   " ++ pprintType 0 actual
    ]
  show (KindMismatch expected actual) = unlines
    ["type mismatch:"
    ,"expected: " ++ pprintKind expected
    ,"actual:   " ++ pprintKind actual
    ]
  show (NotInScope x) = "variable not in scope: " ++ show x
  show (CtorNotInScope c) = "constructor not in scope: " ++ show c
  show (TyNotInScope aa) = "type variable not in scope: " ++ show aa
  show (TyConNotInScope tc) = "type constructor not in scope: " ++ show tc
  show (CannotApply t) = "value of type " ++ pprintType 0 t ++ " cannot have a value applied to it"
  show (CannotInstantiate t) = "value of type " ++ pprintType 0 t ++ " cannot have a type applied to it"
  show (CannotProject t) = "cannot project field from value of type " ++ pprintType 0 t
  show (InvalidLetRec f) = "invalid definition " ++ show f ++ " in a letrec binding"

newtype TC a = TC { runTC :: ReaderT TCEnv (Except TCError) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader TCEnv TC
deriving newtype instance MonadError TCError TC

data TCEnv
  = TCEnv {
    tcTmVars :: Map TmVar Type
  , tcTyVars :: Map TyVar Kind
  , tcCtors :: Map Ctor Type
  , tcTyCons :: Map TyCon Kind
  }

withVars :: [(TmVar, Type)] -> TC a -> TC a
withVars xs m = do
  traverse_ (\ (_, t) -> checkType t KiStar) xs
  local f m
  where
    f (TCEnv tms tys cs tcs) = TCEnv (foldr (uncurry Map.insert) tms xs) tys cs tcs

withTyVars :: [(TyVar, Kind)] -> TC a -> TC a
withTyVars aas = local f
  where
    f (TCEnv tms tys cs tcs) = TCEnv tms (foldr (uncurry Map.insert) tys aas) cs tcs

withCtors :: [(Ctor, Type)] -> TC a -> TC a
withCtors ctors = local f
  where
    f (TCEnv tms tys cs tcs) = TCEnv tms tys (foldr (uncurry Map.insert) cs ctors) tcs

withTyCons :: [(TyCon, Kind)] -> TC a -> TC a
withTyCons tctors = local f
  where
    f (TCEnv tms tys cs tcs) = TCEnv tms tys cs (foldr (uncurry Map.insert) tcs tctors)

infer :: Term -> TC Type
infer (TmVarOcc x) = do
  env <- asks tcTmVars
  case Map.lookup x env of
    Just t -> pure t
    Nothing -> throwError (NotInScope x)
infer (TmCtorOcc c) = do
  env <- asks tcCtors
  case Map.lookup c env of
    Just t -> pure t
    Nothing -> throwError (CtorNotInScope c)
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
    TyAll aa ki t' -> do
      checkType t ki
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
infer (TmCaseSum e c (xl, tl, el) (xr, tr, er)) = do
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

-- | 'inferType' computes the kind of its argument.
inferType :: Type -> TC Kind
inferType (TyAll aa ki t) = withTyVars [(aa, ki)] $ inferType t
inferType (TyVarOcc aa) = do
  env <- asks tcTyVars
  case Map.lookup aa env of
    Nothing -> throwError (TyNotInScope aa)
    Just ki -> pure ki
inferType TyUnit = pure KiStar
inferType TyInt = pure KiStar
inferType TyString = pure KiStar
inferType TyBool = pure KiStar
inferType (TyList t) = inferType t
inferType (TySum t s) = inferType t *> inferType s
inferType (TyProd t s) = inferType t *> inferType s
inferType (TyArr t s) = inferType t *> inferType s
inferType (TyApp t s) = do
  inferType t >>= \case
    KiStar -> throwError (CannotTyApp t)
inferType (TyConOcc tc) = do
  env <- asks tcTyCons
  case Map.lookup tc env of
    Nothing -> throwError (TyConNotInScope tc)
    Just ki -> pure ki

checkType :: Type -> Kind -> TC ()
checkType t k = do
  k' <- inferType t
  when (k' /= k) $ throwError (KindMismatch k k')

checkDataDecls :: [DataDecl] -> TC ([(TyCon, Kind)], [(Ctor, Type)])
checkDataDecls ds = flip execStateT ([], []) $ do
  traverse_ f ds
  where
    f (DataDecl tc params ctors) = do
      let ki = KiStar -- TODO: Use type parameters here. (Need KiArr)
      modify (\ (tcs, cs) -> ((tc, ki) : tcs, cs))
      ctorbinds <- lift $ withTyCons [(tc, ki)] $ do
        withTyVars params $ traverse (checkCtorDecl tc params) ctors
      modify (\ (tcs, cs) -> (tcs, ctorbinds ++ cs))


checkCtorDecl :: TyCon -> [(TyVar, Kind)] -> CtorDecl -> TC (Ctor, Type)
checkCtorDecl tc params (CtorDecl c args) = do
  traverse_ (\arg -> checkType arg KiStar) args
  let ctorRet = foldl TyApp (TyConOcc tc) (map (TyVarOcc . fst) params)
  let ctorTy = foldr (uncurry TyAll) (foldr TyArr ctorRet args) params
  pure (c, ctorTy)

checkProgram :: Program -> Either TCError ()
checkProgram (Program ds e) = runExcept . flip runReaderT emptyEnv $ runTC $ do
  (tyconbinds, ctorbinds) <- checkDataDecls ds
  _ <- withTyCons tyconbinds $ withCtors ctorbinds $ infer e
  pure ()
  where emptyEnv = TCEnv Map.empty Map.empty Map.empty Map.empty

