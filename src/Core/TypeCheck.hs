
module Core.TypeCheck
    ( checkProgram
    ) where

import Core.IR

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Foldable (traverse_, for_)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State


insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs


data TCError
  -- Things not in scope
  = NotInScope TmVar
  | CtorNotInScope Ctor
  | TyNotInScope TyVar
  | TyConNotInScope TyCon
  | AliasNotInScope Alias

  -- Mismatch between expected and actual
  | TypeMismatch Type Type -- expected, actual
  | KindMismatch Kind Kind -- expected, actual
  | ArityMismatch

  -- Cannot eliminate subject in this manner
  | CannotProject Type
  | CannotApply Type
  | CannotTyApp Type
  | CannotInstantiate Type
  | CannotScrutinize Type
  | NotMonadic Type

  -- Misc.
  | InvalidLetRec TmVar
  | BadCaseLabels

instance Show TCError where
  show (TypeMismatch expected actual) = unlines
    ["type mismatch:"
    ,"expected: " ++ pprintType 0 expected
    ,"actual:   " ++ pprintType 0 actual
    ]
  show (KindMismatch expected actual) = unlines
    ["kind mismatch:"
    ,"expected: " ++ pprintKind expected
    ,"actual:   " ++ pprintKind actual
    ]
  show ArityMismatch = "wrong number of parameters or arguments"
  show (NotInScope x) = "variable not in scope: " ++ show x
  show (CtorNotInScope c) = "constructor not in scope: " ++ show c
  show (TyNotInScope aa) = "type variable not in scope: " ++ show aa
  show (TyConNotInScope tc) = "type constructor not in scope: " ++ show tc
  show (AliasNotInScope al) = "type alias not in scope: " ++ show al
  show (CannotApply t) = "value of type " ++ pprintType 0 t ++ " cannot have a value applied to it"
  show (CannotInstantiate t) = "value of type " ++ pprintType 0 t ++ " cannot have a type applied to it"
  show (CannotProject t) = "cannot project field from value of type " ++ pprintType 0 t
  show (NotMonadic t) = "cannot execute value with non-monadic type " ++ pprintType 0 t
  show (InvalidLetRec f) = "invalid definition " ++ show f ++ " in a letrec binding"
  show (CannotTyApp t) = "cannot apply type " ++ pprintType 0 t ++ " to an argument"
  show (CannotScrutinize t) = "cannot perform case analysis on type " ++ pprintType 0 t
  show BadCaseLabels = "too many/too few/duplicate ctors in a case analysis"


newtype TC a = TC { getTC :: StateT Signature (ReaderT TCEnv (Except TCError)) a }

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT emptyEnv . flip evalStateT emptySig . getTC
  where
    emptyEnv = TCEnv Map.empty Map.empty Map.empty
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
  , tcAliases :: Map Alias AliasDef
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
    f env = env { tcTmVars = insertMany xs (tcTmVars env) }

withTyVars :: [(TyVar, Kind)] -> TC a -> TC a
withTyVars aas = local f
  where
    f env = env { tcTyVars = insertMany aas (tcTyVars env) }

withAlias :: Alias -> AliasDef -> TC a -> TC a
withAlias al ad m = do
  checkAliasDef ad
  let extend env = env { tcAliases = Map.insert al ad (tcAliases env) }
  local extend m

lookupVar :: TmVar -> TC Type
lookupVar x = do
  env <- asks tcTmVars
  case Map.lookup x env of
    Nothing -> throwError (NotInScope x)
    Just t -> pure t

lookupTyVar :: TyVar -> TC Kind
lookupTyVar aa = do
  env <- asks tcTyVars
  case Map.lookup aa env of
    Nothing -> throwError (TyNotInScope aa)
    Just ki -> pure ki

lookupAlias :: Alias -> TC AliasDef
lookupAlias al = do
  env <- asks tcAliases
  case Map.lookup al env of
    Nothing -> throwError (AliasNotInScope al)
    Just ad -> pure ad

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
equalTypes t t' = do
  env <- asks tcAliases
  unless (eqType (emptyAE env) t t') $ throwError (TypeMismatch t t')

equalKinds :: Kind -> Kind -> TC ()
equalKinds k k' = when (k' /= k) $ throwError (KindMismatch k k')

-- | Push a type alias at the outermost level out of the way, by substituting
-- it into the body.
push :: Type -> TC Type
push (TyAliasApp al args) = do
  AliasDef params k t <- lookupAlias al
  checkTyArgs params args
  let sub = makeSubst [(aa, s) | ((aa, k), s) <- zip params args]
  push (substType sub t)
push t = pure t


-- | Infer the type of a term.
infer :: Term -> TC Type
infer (TmVarOcc x) = lookupVar x
infer (TmCtorOcc c) = lookupCtor c
infer (TmLet x t e1 e2) = do
  check e1 t
  withVars [(x, t)] $ infer e2
infer (TmLetType al ad e) = do
  withAlias al ad $ infer e

infer (TmLetRec bs e) = do
  for_ bs $ \ (x, _, rhs) -> case rhs of
    TmLam _ _ _ -> pure ()
    TmTLam _ _ _ -> pure ()
    _ -> throwError (InvalidLetRec x)
  let binds = [(x, t) | (x, t, _) <- bs]
  withVars binds $ traverse_ (\ (_, t, e') -> check e' t) bs
  withVars binds $ infer e

infer (TmBool _) = pure TyBool
infer (TmInt _) = pure TyInt
infer (TmString _) = pure TyString
infer (TmChar _) = pure TyChar

infer (TmLam x t e) = do
  t' <- withVars [(x, t)] $ infer e
  pure (TyArr t t')
infer (TmApp e1 e2) = do
  (infer >=> push) e1 >>= \case
    TyArr t1 t2 -> do
      check e2 t1
      pure t2
    t -> throwError (CannotApply t)

infer (TmTLam aa ki e) = do
  t <- withTyVars [(aa, ki)] $ infer e
  pure (TyAll aa ki t)
infer (TmTApp e t) = do
  (infer >=> push) e >>= \case
    TyAll aa ki t' -> do
      checkType t ki
      pure (substType (singleSubst aa t) t')
    t' -> throwError (CannotInstantiate t')

infer TmNil = pure TyUnit
infer (TmPair e1 e2) = TyProd <$> infer e1 <*> infer e2
infer (TmRecord fs) = TyRecord <$> traverse (\ (f, e) -> (,) <$> pure f <*> infer e) fs
infer (TmFst e) = do
  (infer >=> push) e >>= \case
    TyProd t1 _t2 -> pure t1
    t -> throwError (CannotProject t)
infer (TmSnd e) = do
  (infer >=> push) e >>= \case
    TyProd _t1 t2 -> pure t2
    t -> throwError (CannotProject t)
infer (TmFieldProj e f) = do
  (infer >=> push) e >>= \case
    t@(TyRecord fs) -> case lookup f fs of
      Nothing -> throwError (CannotProject t)
      Just t' -> pure t'
    t -> throwError (CannotProject t)

infer (TmArith e1 _ e2) = do
  check e1 TyInt
  check e2 TyInt
  pure TyInt
infer (TmNegate e) = do
  check e TyInt
  pure TyInt
infer (TmCmp e1 TmCmpEqChar e2) = check e1 TyChar *> check e2 TyChar *> pure TyBool
infer (TmCmp e1 _ e2) = do
  check e1 TyInt
  check e2 TyInt
  pure TyBool
infer (TmStringOp e1 TmConcat e2) = check e1 TyString *> check e2 TyString *> pure TyString
infer (TmStringOp e1 TmIndexStr e2) = check e1 TyString *> check e2 TyInt *> pure TyChar
infer (TmStringLength e1) = check e1 TyString *> pure TyInt

infer (TmIf ec s et ef) = inferIf ec s et ef
infer (TmCase e s alts) = inferCase e s alts

infer (TmPure e) = do
  t <- infer e
  pure (TyIO t)
infer (TmBind x t e1 e2) = do
  check e1 (TyIO t)
  withVars [(x, t)] $ infer e2
infer TmGetLine = pure (TyIO TyString)
infer (TmPutLine e) = do
  check e TyString
  pure (TyIO TyUnit)
infer (TmRunIO e) = do
  (infer >=> push) e >>= \case
    TyIO t -> pure t
    t' -> throwError (NotMonadic t')

-- | Infer the type of an if-expression.
inferIf :: Term -> Type -> Term -> Term -> TC Type
inferIf ec s et ef = do
  let alts = [(Ctor "false", [], ef), (Ctor "true", [], et)]
  check ec TyBool
  let branchTys = Map.fromList [(Ctor "false", []), (Ctor "true", [])]
  checkBranches alts branchTys s
  pure s

-- | Infer the type of a case-expression .
inferCase :: Term -> Type -> [(Ctor, [(TmVar, Type)], Term)] -> TC Type
inferCase e s alts = do
  tcapp <- (infer >=> push) e >>= \t -> case asTyConApp t of
    Just tapp -> pure tapp
    Nothing -> throwError (CannotScrutinize t)
  branchTys <- instantiateTyConApp tcapp
  checkBranches alts branchTys s
  pure s

instantiateTyConApp :: TyConApp -> TC (Map Ctor [Type])
instantiateTyConApp tcapp = case tcapp of
  TyConApp tc args -> do
    DataDecl _ params ctors <- lookupTyCon tc
    let sub = makeSubst (zipWith (\ (aa, _) t -> (aa, t)) params args)
    pure $ Map.fromList $ map (ctorBranchTy sub) ctors
  where
    ctorBranchTy :: Subst -> CtorDecl -> (Ctor, [Type])
    ctorBranchTy sub (CtorDecl c ctorArgs) = (c, map (substType sub) ctorArgs)

checkBranches :: [(Ctor, [(TmVar, Type)], Term)] -> Map Ctor [Type] -> Type -> TC ()
checkBranches alts branchTys s = do
  let provided = Set.fromList (map (\ (c, _, _) -> c) alts)
  let required = Map.keysSet branchTys
  when (provided /= required) $
    throwError BadCaseLabels
  for_ alts $ \ (c, xs, rhs) -> do
    let argTys = branchTys Map.! c
    checkBinds xs argTys
    withVars xs $ check rhs s

-- | Check that the variables bound by a case alternative have the types
-- indicated by the scrutinee.
checkBinds :: [(TmVar, Type)] -> [Type] -> TC ()
checkBinds [] [] = pure ()
checkBinds ((x, t) : binds) (t' : tys) = equalTypes t t' *> checkBinds binds tys
checkBinds _ _ = throwError ArityMismatch

-- | Check that a sequence of type parameters matches a sequence of type
-- arguments.
checkTyArgs :: [(TyVar, Kind)] -> [Type] -> TC ()
checkTyArgs [] [] = pure ()
checkTyArgs ((aa, ki) : aas) (t : ts) = checkType t ki *> checkTyArgs aas ts
checkTyArgs _ _ = throwError ArityMismatch

-- | Check that a term has the specified type.
check :: Term -> Type -> TC ()
check e t = infer e >>= equalTypes t

-- | Compute the kind of a type.
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
inferType TyChar = pure KiStar
inferType TyBool = pure KiStar
inferType (TyProd t s) = checkType t KiStar *> checkType s KiStar *> pure KiStar
inferType (TyRecord fs) = traverse_ (\ (f, t) -> checkType t KiStar) fs *> pure KiStar
inferType (TyIO t) = checkType t KiStar *> pure KiStar
inferType (TyArr t s) = checkType t KiStar *> checkType s KiStar *> pure KiStar
inferType (TyAliasApp al args) = do
  AliasDef params k _t <- lookupAlias al
  checkTyArgs params args
  pure k

-- | Check that a type has the specified kind.
checkType :: Type -> Kind -> TC ()
checkType t k = inferType t >>= equalKinds k

-- | Compute the kind of a data declaration.
dataDeclKind :: DataDecl -> Kind
dataDeclKind (DataDecl _ params _) = foldr (\ (_, k1) k2 -> KiArr k1 k2) KiStar params

checkAliasDef :: AliasDef -> TC ()
checkAliasDef (AliasDef params k t) = do
  withTyVars params $ checkType t k

-- | Check a data declaration for validity and extend the declaration signature.
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

-- | Check that a program is well-formed.
checkProgram :: Program -> Either TCError ()
checkProgram (Program ds e) = runTC $ do
  traverse_ checkDataDecl ds
  _ <- infer e
  pure ()

