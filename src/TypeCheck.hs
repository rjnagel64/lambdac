
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
  -- Things not in scope
  = NotInScope TmVar
  | CtorNotInScope Ctor
  | TyNotInScope TyVar
  | TyConNotInScope TyCon

  -- Mismatch between expected and actual
  | TypeMismatch Type Type -- expected, actual
  | KindMismatch Kind Kind -- expected, actual

  -- Cannot eliminate subject in this manner
  | CannotProject Type
  | CannotApply Type
  | CannotTyApp Type
  | CannotInstantiate Type
  | CannotScrutinize Type

  -- Misc.
  | InvalidLetRec TmVar
  | MissingCaseAlt Ctor

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

newtype TC a = TC { getTC :: StateT Signature (ReaderT TCEnv (Except TCError)) a }

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT emptyEnv . flip evalStateT emptySig . getTC
  where
    emptyEnv = TCEnv Map.empty Map.empty
    emptySig = Signature Map.empty Map.empty

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader TCEnv TC
deriving newtype instance MonadState Signature TC
deriving newtype instance MonadError TCError TC

data TCEnv
  = TCEnv {
    tcTmVars :: Map TmVar Type
  , tcTyVars :: Map TyVar Kind
  }

data Signature
  = Signature {
    sigTyCons :: Map TyCon DataDecl
  , sigCtors :: Map Ctor Type
  }

withVars :: [(TmVar, Type)] -> TC a -> TC a
withVars xs m = do
  traverse_ (\ (_, t) -> checkType t KiStar) xs
  local f m
  where
    f (TCEnv tms tys) = TCEnv (foldr (uncurry Map.insert) tms xs) tys

lookupVar :: TmVar -> TC Type
lookupVar x = do
  env <- asks tcTmVars
  case Map.lookup x env of
    Just t -> pure t
    Nothing -> throwError (NotInScope x)

withTyVars :: [(TyVar, Kind)] -> TC a -> TC a
withTyVars aas = local f
  where
    f (TCEnv tms tys) = TCEnv tms (foldr (uncurry Map.insert) tys aas)

lookupTyVar :: TyVar -> TC Kind
lookupTyVar aa = do
  env <- asks tcTyVars
  case Map.lookup aa env of
    Nothing -> throwError (TyNotInScope aa)
    Just ki -> pure ki

lookupCtor :: Ctor -> TC Type
lookupCtor c = do
  env <- gets sigCtors
  case Map.lookup c env of
    Just t -> pure t
    Nothing -> throwError (CtorNotInScope c)

lookupTyCon :: TyCon -> TC DataDecl
lookupTyCon tc = do
  env <- gets sigTyCons
  case Map.lookup tc env of
    Nothing -> throwError (TyConNotInScope tc)
    Just dd -> pure dd

equalTypes :: Type -> Type -> TC ()
equalTypes t t' = when (t /= t') $ throwError (TypeMismatch t t')

equalKinds :: Kind -> Kind -> TC ()
equalKinds k k' = when (k' /= k) $ throwError (KindMismatch k k')


infer :: Term -> TC Type
infer (TmVarOcc x) = lookupVar x
infer (TmCtorOcc c) = lookupCtor c
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

infer (TmInl a b e) = do
  check e a
  pure (TySum a b)
infer (TmInr a b e) = do
  check e b
  pure (TySum a b)

infer (TmEmpty t) = pure (TyList t)
infer (TmCons t e1 e2) = do
  check e1 t
  check e2 (TyList t)
  pure (TyList t)

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

infer (TmIf ec s et ef) = do
  let alts = [(Ctor "false", [], ef), (Ctor "true", [], et)]
  inferCase ec s alts
infer (TmCaseSum e s (xl, tl, el) (xr, tr, er)) = do
  let alts = [(Ctor "inl", [(xl, tl)], el), (Ctor "inr", [(xr, tr)], er)]
  inferCase e s alts
infer (TmCaseList e s enil ((xhead, thead), (xtail, ttail), econs)) = do
  let alts = [(Ctor "nil", [], enil), (Ctor "cons", [(xhead, thead), (xtail, ttail)], econs)]
  inferCase e s alts
infer (TmCase e s alts) = inferCase e s alts

inferCase :: Term -> Type -> [(Ctor, [(TmVar, Type)], Term)] -> TC Type
inferCase e s alts = do
  tcapp <- infer e >>= \t -> case asTyConApp t of
    Just tapp -> pure tapp
    Nothing -> throwError (CannotScrutinize t)
  branchTys <- tyConBranchTypes tcapp

  -- Hmm. This will find missing alts, but will not find duplicate alts or alts
  -- from a different data type.
  --
  -- Check that separately, I guess.
  for_ branchTys $ \ (c, argTys) -> do
    -- Check that alt with matching ctor exists
    (binds, rhs) <- findAlt c alts
    -- Check that bindings on that alt have correct annotations
    checkBinds binds argTys
    -- Check that RHS has return type 's'.
    withVars binds $ check rhs s

  pure s

tyConBranchTypes :: TyConApp -> TC [(Ctor, [Type])]
tyConBranchTypes tcapp = case tcapp of
  CaseBool -> pure [(Ctor "false", []), (Ctor "true", [])]
  CaseSum t s -> pure [(Ctor "inl", [t]), (Ctor "inr", [s])]
  CaseList t -> pure [(Ctor "nil", []), (Ctor "cons", [t, TyList t])]
  -- Lookup tc. Make subst [params := args]. Use subst on each ctordecl to get branches.
  TyConApp tc args -> do
    DataDecl _ params ctors <- lookupTyCon tc
    let sub = makeSubst (zipWith (\ (aa, _) t -> (aa, t)) params args)
    pure $ map (ctorBranchTy sub) ctors
  where
    ctorBranchTy :: Subst -> CtorDecl -> (Ctor, [Type])
    ctorBranchTy sub (CtorDecl c ctorArgs) = (c, map (substType sub) ctorArgs)

findAlt :: Ctor -> [(Ctor, [(TmVar, Type)], Term)] -> TC ([(TmVar, Type)], Term)
findAlt c [] = throwError (MissingCaseAlt c)
findAlt c ((c', binds, rhs) : alts) =
  if c == c' then
    pure (binds, rhs)
  else
    findAlt c alts

checkBinds :: [(TmVar, Type)] -> [Type] -> TC ()
checkBinds [] [] = pure ()
checkBinds ((x, t) : binds) (t' : tys) = equalTypes t t' *> checkBinds binds tys

check :: Term -> Type -> TC ()
check e t = infer e >>= equalTypes t

checkFun :: TmFun -> TC ()
checkFun (TmFun _f x t s e) = do
  withVars [(x, t)] $ check e s
checkFun (TmTFun _f aa ki t e) = do
  withTyVars [(aa, ki)] $ check e t

-- | 'inferType' computes the kind of its argument.
inferType :: Type -> TC Kind
inferType (TyVarOcc aa) = lookupTyVar aa
inferType (TyConOcc tc) = dataDeclKind <$> lookupTyCon tc
inferType (TyAll aa ki t) = withTyVars [(aa, ki)] $ inferType t
inferType (TyApp t s) = do
  inferType t >>= \case
    KiStar -> throwError (CannotTyApp t)
    KiArr k1 k2 -> checkType s k1 *> pure k2
inferType TyUnit = pure KiStar
inferType TyInt = pure KiStar
inferType TyString = pure KiStar
inferType TyBool = pure KiStar
inferType (TyList t) = checkType t KiStar *> pure KiStar
inferType (TySum t s) = checkType t KiStar *> checkType s KiStar *> pure KiStar
inferType (TyProd t s) = checkType t KiStar *> checkType s KiStar *> pure KiStar
inferType (TyArr t s) = checkType t KiStar *> checkType s KiStar *> pure KiStar

checkType :: Type -> Kind -> TC ()
checkType t k = inferType t >>= equalKinds k

dataDeclKind :: DataDecl -> Kind
dataDeclKind (DataDecl _ params _) = foldr (\ (_, k1) k2 -> KiArr k1 k2) KiStar params

checkDataDecls :: [DataDecl] -> TC ()
checkDataDecls ds = traverse_ checkDataDecl ds 

checkDataDecl :: DataDecl -> TC ()
checkDataDecl dd@(DataDecl tc params ctors) = do
  modify (\ (Signature tcs cs) -> Signature (Map.insert tc dd tcs) cs)
  withTyVars params $ traverse_ (checkCtorDecl tc params) ctors

checkCtorDecl :: TyCon -> [(TyVar, Kind)] -> CtorDecl -> TC ()
checkCtorDecl tc params (CtorDecl c args) = do
  traverse_ (\arg -> checkType arg KiStar) args
  let ctorRet = TyConApp tc (map (TyVarOcc . fst) params)
  let ctorTy = foldr (uncurry TyAll) (foldr TyArr (fromTyConApp ctorRet) args) params
  modify (\ (Signature tcs cs) -> Signature tcs (Map.insert c ctorTy cs))

checkProgram :: Program -> Either TCError ()
checkProgram (Program ds e) = runTC $ do
  checkDataDecls ds
  _ <- infer e
  pure ()

