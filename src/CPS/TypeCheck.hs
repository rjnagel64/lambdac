
-- | Check that a CPS'ed program is well-typed.
module CPS.TypeCheck (checkProgram, TypeError(..)) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set

import Data.Foldable (for_, traverse_)

import CPS.IR

import Prelude hiding (cos)


data TypeError
  = TmNotInScope TmVar
  | CoNotInScope CoVar
  | TyNotInScope TyVar
  | TyConNotInScope TyCon
  | TypeMismatch TypeK TypeK
  | CoTypeMismatch CoTypeK CoTypeK
  | KindMismatch KindK KindK
  | BadCaseAnalysis TmVar TypeK
  | BadCaseLabels
  | ArityMismatch
  | BadValue ValueK TypeK
  | InvalidCtor Ctor TyCon
  | BadProjection TypeK
  | CannotCall TmVar TypeK
  | CannotInst TmVar TypeK
  | CannotTyApp TypeK

instance Show TypeError where
  show (TmNotInScope x) = "term variable " ++ show x ++ " not in scope"
  show (CoNotInScope k) = "continuation variable " ++ show k ++ " not in scope"
  show (TyNotInScope aa) = "type variable " ++ show aa ++ " not in scope"
  show (TyConNotInScope tc) = "type constructor " ++ show tc ++ " not in scope"
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
  show BadCaseLabels = "too many/too few/wrong constructors in case branches"
  show ArityMismatch = "incorrect arity"
  show (BadValue v t) = "value " ++ pprintValue v ++ " does not have expected type " ++ pprintType t
  show (BadProjection t) = "cannot project a field from value of type " ++ pprintType t
  show (CannotCall f t) = 
    "variable " ++ show f ++ " is applied to arguments but its type is not a function: "
    ++ pprintType t
  show (CannotInst f t) = 
    "variable " ++ show f ++ " is applied to type arguments but its type is not a forall: "
    ++ pprintType t
  show (CannotTyApp t) =
    "cannot apply argument to type " ++ pprintType t ++ " because it does not have an arrow kind"
  show (InvalidCtor c tc) =
    show c ++ " is not a constructor of type " ++ show tc

newtype TC a = TC { getTC :: StateT Signature (ReaderT Context (Except TypeError)) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader Context TC
deriving newtype instance MonadState Signature TC
deriving newtype instance MonadError TypeError TC

runTC :: TC a -> Either TypeError a
runTC = runExcept . flip runReaderT emptyContext . flip evalStateT emptySignature . getTC

data Context
  = Context {
    tmContext :: Map TmVar TypeK
  , coContext :: Map CoVar CoTypeK
  , tyContext :: Map TyVar KindK
  }

data Signature
  = Signature {
    sigTyCons :: Map TyCon DataDecl
  }

emptyContext :: Context
emptyContext = Context Map.empty Map.empty Map.empty

emptySignature :: Signature
emptySignature = Signature Map.empty

withTmVars :: [(TmVar, TypeK)] -> TC a -> TC a
withTmVars [] m = m
withTmVars ((x, t) : binds) m = checkType t StarK *> local extend (withTmVars binds m)
  where extend (Context tms cos tys) = Context (Map.insert x t tms) cos tys

withCoVars :: [(CoVar, CoTypeK)] -> TC a -> TC a
withCoVars [] m = m
withCoVars ((k, s) : binds) m = checkCoType s StarK *> local extend (withCoVars binds m)
  where extend (Context tms cos tys) = Context tms (Map.insert k s cos) tys

withTyVars :: [(TyVar, KindK)] -> TC a -> TC a
withTyVars [] m = m
withTyVars ((aa, kk) : binds) m = checkKind kk *> local extend (withTyVars binds m)
  where extend (Context tms cos tys) = Context tms cos (Map.insert aa kk tys)

lookupTmVar :: TmVar -> TC TypeK
lookupTmVar x = asks tmContext >>= maybe err pure . Map.lookup x
  where err = throwError (TmNotInScope x)

lookupCoVar :: CoVar -> TC CoTypeK
lookupCoVar x = asks coContext >>= maybe err pure . Map.lookup x
  where err = throwError (CoNotInScope x)

lookupTyVar :: TyVar -> TC KindK
lookupTyVar x = asks tyContext >>= maybe err pure . Map.lookup x
  where err = throwError (TyNotInScope x)

lookupTyCon :: TyCon -> TC DataDecl
lookupTyCon x = gets sigTyCons >>= maybe err pure . Map.lookup x
  where err = throwError (TyConNotInScope x)

dataDeclKind :: DataDecl -> KindK
dataDeclKind (DataDecl _ params _) = foldr (\ (_, k1) k2 -> KArrK k1 k2) StarK params

equalTypes :: TypeK -> TypeK -> TC ()
equalTypes expected actual =
  unless (eqTypeK expected actual) $ throwError (TypeMismatch expected actual)

equalCoTypes :: CoTypeK -> CoTypeK -> TC ()
equalCoTypes expected actual =
  unless (eqCoTypeK expected actual) $ throwError (CoTypeMismatch expected actual)

equalKinds :: KindK -> KindK -> TC ()
equalKinds expected actual =
  unless (expected == actual) $ throwError (KindMismatch expected actual)

-- Hmm. Constructing the substitution duplicates logic in parameterSubst.
-- Generalize, deduplicate.
instantiate :: [(TyVar, KindK)] -> [TypeK] -> [CoTypeK] -> TC [CoTypeK]
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


checkProgram :: Program () -> Either TypeError ()
checkProgram (Program ds e) = runTC $ do
  withDataDecls ds $ check e

withDataDecls :: [DataDecl] -> TC a -> TC a
withDataDecls [] m = m
withDataDecls (dd@(DataDecl tc params ctors) : ds) m = do
  modify (\ (Signature tcs) -> Signature (Map.insert tc dd tcs))
  withTyVars params $ traverse_ checkCtorDecl ctors
  withDataDecls ds m

-- Hmm. Do I need to record ctor -> type bindings? (or ctor -> tycon? or anything?)
checkCtorDecl :: CtorDecl -> TC ()
checkCtorDecl (CtorDecl c args) = traverse_ (\t -> checkType t StarK) args


check :: TermK a -> TC ()
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
check (CaseK x s ks) = checkCase x s ks
check (LetContK ks e) = do
  for_ ks $ \ (ContDef _ _ xs e') -> do
    withTmVars xs $ check e'
  let defs = map (\k -> (contDefName k, contDefType k)) ks
  withCoVars defs $ check e
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

checkCase :: TmVar -> TyConApp -> [(Ctor, CoVar)] -> TC ()
checkCase x CaseBool ks =
  checkTmVar x BoolK *>
  checkBranches ks (Map.fromList [(Ctor "false", []), (Ctor "true", [])])
checkCase x (CaseSum t1 t2) ks =
  checkTmVar x (SumK t1 t2) *>
  checkBranches ks (Map.fromList [(Ctor "inl", [t1]), (Ctor "inr", [t2])])
checkCase x tcapp ks = do
  checkTmVar x (fromTyConApp tcapp)
  branchTys <- instantiateTyConApp tcapp
  checkBranches ks branchTys

checkBranches :: [(Ctor, CoVar)] -> Map Ctor [TypeK] -> TC ()
checkBranches branches branchTys = do
  let provided = Set.fromList (map fst branches)
  let required = Map.keysSet branchTys
  -- Not quite correct. Does not detect duplicate provided ctors
  when (provided /= required) $
    throwError BadCaseLabels
  for_ branches $ \ (c, k) -> do
    let branchTy = branchTys Map.! c
    checkCoVar k (ContK branchTy)

checkArith :: ArithK -> TC ()
checkArith (AddK x y) = checkIntBinOp x y
checkArith (SubK x y) = checkIntBinOp x y
checkArith (MulK x y) = checkIntBinOp x y
checkArith (NegK x) = checkTmVar x IntK

checkCompare :: CmpK -> TC ()
checkCompare (CmpEqK x y) = checkIntBinOp x y
checkCompare (CmpNeK x y) = checkIntBinOp x y
checkCompare (CmpLtK x y) = checkIntBinOp x y
checkCompare (CmpLeK x y) = checkIntBinOp x y
checkCompare (CmpGtK x y) = checkIntBinOp x y
checkCompare (CmpGeK x y) = checkIntBinOp x y

checkIntBinOp :: TmVar -> TmVar -> TC ()
checkIntBinOp x y = do
  checkTmVar x IntK
  checkTmVar y IntK

checkValue :: ValueK -> TypeK -> TC ()
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
checkValue v@(CtorAppK c xs) t = case asTyConApp t of
  Nothing -> throwError (BadValue v t)
  Just tcapp -> checkCtorApp c xs tcapp
checkValue v t = throwError (BadValue v t)

checkCtorApp :: Ctor -> [TmVar] -> TyConApp -> TC ()
checkCtorApp c args tcapp@(TyConApp tc _) = do
  ctors <- instantiateTyConApp tcapp
  case Map.lookup c ctors of
    Nothing -> throwError (InvalidCtor c tc)
    Just argTys -> checkCtorArgs args argTys

instantiateTyConApp :: TyConApp -> TC (Map Ctor [TypeK])
instantiateTyConApp (TyConApp tc tys) = do
  DataDecl _ params ctors <- lookupTyCon tc
  sub <- parameterSubst params tys
  let cs = Map.fromList [(c, map (substTypeK sub) argTys) | CtorDecl c argTys <- ctors]
  pure cs

parameterSubst :: [(TyVar, KindK)] -> [TypeK] -> TC Subst
parameterSubst params args = makeSubst <$> go params args
  where
    go [] [] = pure []
    go ((aa, k) : aas) (t : ts) = checkType t k *> fmap ((aa, t) :) (go aas ts)
    go _ _ = throwError ArityMismatch

checkCtorArgs :: [TmVar] -> [TypeK] -> TC ()
checkCtorArgs [] [] = pure ()
checkCtorArgs (x : xs) (t : ts) = checkTmVar x t *> checkCtorArgs xs ts
checkCtorArgs _ _ = throwError ArityMismatch

checkTmVar :: TmVar -> TypeK -> TC ()
checkTmVar x t = do
  t' <- lookupTmVar x
  equalTypes t t'

checkCoVar :: CoVar -> CoTypeK -> TC ()
checkCoVar x t = do
  t' <- lookupCoVar x
  equalCoTypes t t'

checkTmArgs :: [TmVar] -> [TypeK] -> TC ()
checkTmArgs [] [] = pure ()
checkTmArgs (x:xs) (s:ss) = checkTmVar x s *> checkTmArgs xs ss
checkTmArgs _ _ = throwError ArityMismatch

checkCoArgs :: [CoVar] -> [CoTypeK] -> TC ()
checkCoArgs [] [] = pure ()
checkCoArgs (k:ks) (s:ss) = checkCoVar k s *> checkCoArgs ks ss
checkCoArgs _ _ = throwError ArityMismatch


-- | Check that a type has the given kind.
inferType :: TypeK -> TC KindK
inferType (TyVarOccK aa) = lookupTyVar aa
inferType (TyConOccK tc) = dataDeclKind <$> lookupTyCon tc
inferType (AllK aas ss) =
  withTyVars aas (traverse_ (\s -> checkCoType s StarK) ss) *>
  pure StarK
inferType (FunK ts ss) =
  traverse_ (\t -> checkType t StarK) ts *>
  traverse_ (\s -> checkCoType s StarK) ss *>
  pure StarK
inferType (ProdK t s) = checkType t StarK *> checkType s StarK *> pure StarK
inferType (SumK t s) = checkType t StarK *> checkType s StarK *> pure StarK
inferType UnitK = pure StarK
inferType IntK = pure StarK
inferType BoolK = pure StarK
inferType StringK = pure StarK
inferType (TyAppK t s) =
  inferType t >>= \case
    KArrK k1 k2 -> checkType s k1 *> pure k2
    StarK -> throwError (CannotTyApp t)

-- | Check that a co-type has the given kind.
inferCoType :: CoTypeK -> TC KindK
inferCoType (ContK ts) = traverse_ (\t -> checkType t StarK) ts *> pure StarK

checkType :: TypeK -> KindK -> TC ()
checkType t k = inferType t >>= equalKinds k

checkCoType :: CoTypeK -> KindK -> TC ()
checkCoType t k = inferCoType t >>= equalKinds k

-- | Check that a kind is well-formed.
-- This is basically redundant, because kinds are trivial values, but it's
-- consistent with other things, I guess.
checkKind :: KindK -> TC ()
checkKind StarK = pure ()
checkKind (KArrK k1 k2) = checkKind k1 *> checkKind k2
