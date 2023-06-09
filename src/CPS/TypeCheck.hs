
-- | Check that a CPS'ed program is well-typed.
module CPS.TypeCheck (checkProgram, TypeError(..)) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set

import Data.Foldable (for_, traverse_)
import Data.Traversable (for)

import CPS.IR

import Prelude hiding (cos)


data TypeError
  = TmVarNotInScope TmVar
  | CoVarNotInScope CoVar
  | TyVarNotInScope TyVar
  | TyConNotInScope TyCon
  | CtorNotInScope Ctor
  | TypeMismatch TypeK TypeK
  | LabelMismatch FieldLabel FieldLabel
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
  show (TmVarNotInScope x) = "term variable " ++ show x ++ " not in scope"
  show (CoVarNotInScope k) = "continuation variable " ++ show k ++ " not in scope"
  show (TyVarNotInScope aa) = "type variable " ++ show aa ++ " not in scope"
  show (TyConNotInScope tc) = "type constructor " ++ show tc ++ " not in scope"
  show (CtorNotInScope c) = "constructor " ++ show c ++ " not in scope"
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
  show (LabelMismatch expected actual) = unlines
    [ "field mismatch:"
    , "expected label: " ++ show expected
    , "actual label:   " ++ show actual
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
  , tcContext :: Map TyCon KindK
  , ctContext :: Map Ctor CtorType
  }

-- Hmm. Re-do this to use local scoping, not global signature
data Signature
  = Signature {
    sigTyCons :: Map TyCon DataDecl
  }

-- constructors have types of the form forall (aa : k)+. ss+ -> T aa+
data CtorType = CtorType [(TyVar, KindK)] [TypeK] TyConApp

emptyContext :: Context
emptyContext =
  Context {
    tmContext = Map.empty
  , coContext = Map.empty
  , tyContext = Map.empty
  , tcContext = Map.empty
  , ctContext = Map.empty
  }

emptySignature :: Signature
emptySignature = Signature Map.empty

withTmVars :: [(TmVar, TypeK)] -> TC a -> TC a
withTmVars [] m = m
withTmVars ((x, t) : binds) m = checkType t StarK *> local extend (withTmVars binds m)
  where extend ctx = ctx { tmContext = Map.insert x t (tmContext ctx) }

withCoVars :: [(CoVar, CoTypeK)] -> TC a -> TC a
withCoVars [] m = m
withCoVars ((k, s) : binds) m = checkCoType s StarK *> local extend (withCoVars binds m)
  where extend ctx = ctx { coContext = Map.insert k s (coContext ctx) }

withTyVars :: [(TyVar, KindK)] -> TC a -> TC a
withTyVars [] m = m
withTyVars ((aa, kk) : binds) m = checkKind kk *> local extend (withTyVars binds m)
  where extend ctx = ctx { tyContext = Map.insert aa kk (tyContext ctx) }

withTyCon :: TyCon -> KindK -> TC a -> TC a
withTyCon tc kk m = checkKind kk *> local extend m
  where extend ctx = ctx { tcContext = Map.insert tc kk (tcContext ctx) }

lookupTmVar :: TmVar -> TC TypeK
lookupTmVar x = asks tmContext >>= maybe err pure . Map.lookup x
  where err = throwError (TmVarNotInScope x)

lookupCoVar :: CoVar -> TC CoTypeK
lookupCoVar x = asks coContext >>= maybe err pure . Map.lookup x
  where err = throwError (CoVarNotInScope x)

lookupTyVar :: TyVar -> TC KindK
lookupTyVar x = asks tyContext >>= maybe err pure . Map.lookup x
  where err = throwError (TyVarNotInScope x)

lookupTyCon :: TyCon -> TC KindK
lookupTyCon tc = asks tcContext >>= maybe err pure . Map.lookup tc
  where err = throwError (TyConNotInScope tc)

lookupCtor :: Ctor -> TC CtorType
lookupCtor c = asks ctContext >>= maybe err pure . Map.lookup c
  where err = throwError (CtorNotInScope c)

lookupDataDecl :: TyCon -> TC DataDecl
lookupDataDecl x = gets sigTyCons >>= maybe err pure . Map.lookup x
  where err = throwError (TyConNotInScope x)

equalTypes :: TypeK -> TypeK -> TC ()
equalTypes expected actual =
  unless (eqTypeK expected actual) $ throwError (TypeMismatch expected actual)

equalCoTypes :: CoTypeK -> CoTypeK -> TC ()
equalCoTypes expected actual =
  unless (eqCoTypeK expected actual) $ throwError (CoTypeMismatch expected actual)

equalKinds :: KindK -> KindK -> TC ()
equalKinds expected actual =
  unless (expected == actual) $ throwError (KindMismatch expected actual)



checkProgram :: Program -> Either TypeError ()
checkProgram (Program ds e) = runTC $ do
  withDataDecls ds $ check e

withDataDecls :: [DataDecl] -> TC a -> TC a
withDataDecls [] m = m
withDataDecls (dd@(DataDecl tc k ctors) : ds) m = do
  let extend sig = sig { sigTyCons = Map.insert tc dd (sigTyCons sig) }
  modify extend
  withTyCon tc k $
    withCtorDecls tc ctors $
      withDataDecls ds m

withCtorDecls :: TyCon -> [CtorDecl] -> TC a -> TC a
withCtorDecls tc ctors m = do
  -- check that ctors are distinct
  -- check that ctor types are well-formed
  binds <- traverse (checkCtorDecl tc) ctors
  let extend ctx = ctx { ctContext = foldr (uncurry Map.insert) (ctContext ctx) binds }
  local extend $ m

-- Hmm. Do I need to record ctor -> type bindings? (or ctor -> tycon? or anything?)
checkCtorDecl :: TyCon -> CtorDecl -> TC (Ctor, CtorType)
checkCtorDecl tc (CtorDecl c params args) = do
  withTyVars params $ traverse_ (\t -> checkType t StarK) args
  pure (c, CtorType params args (TyConApp tc [TyVarOccK aa | (aa, _) <- params]))


check :: TermK -> TC ()
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
  sub <- makeSubst aas ts
  let ss' = map (substCoTypeK sub) ss
  checkCoArgs ks ss'
check (IfK x k1 k2) = do
  checkTmVar x BoolK
  checkCoValue (ContValK k1) (ContK [])
  checkCoValue (ContValK k2) (ContK [])
check (CaseK x s ks) = checkCase x s ks
check (LetContK ks e) = do
  defs <- for ks $ \ (k, cont) -> do
    s <- inferContDef cont
    pure (k, s)
  withCoVars defs $ check e
check (LetFunAbsK fs e) = do
  let defs = map (\f -> (funDefName f, funDefType f)) fs
  withTmVars defs $ do
    for_ fs $ \case
      FunDef _ xs ks e' ->
        withTmVars xs $ withCoVars ks $ check e'
      AbsDef _ as ks e' ->
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
check (LetStringOpK z t op e) = do
  t' <- checkStringOp op
  equalTypes t t'
  withTmVars [(z, t)] $ check e
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
check (LetFieldK x s y f e) = do
  lookupTmVar y >>= \case
    t'@(RecordK fs) -> case lookup f fs of
      Nothing -> throwError (BadProjection t')
      Just s' -> equalTypes s s'
    t' -> throwError (BadProjection t')
  withTmVars [(x, s)] $ check e
check (LetBindK s x prim e) = do
  t <- checkPrimIO prim
  withTmVars [(s, TokenK), (x, t)] $ check e

inferContDef :: ContDef -> TC CoTypeK
inferContDef (ContDef xs e) = do
  withTmVars xs $ check e
  pure $ ContK [s | (_, s) <- xs]

checkCase :: TmVar -> TyConApp -> [(Ctor, CoValueK)] -> TC ()
checkCase x tcapp ks = do
  checkTmVar x (fromTyConApp tcapp)
  branchTys <- instantiateTyConApp tcapp
  checkBranches ks branchTys

checkBranches :: [(Ctor, CoValueK)] -> Map Ctor [TypeK] -> TC ()
checkBranches branches branchTys = do
  let provided = Set.fromList (map fst branches)
  let required = Map.keysSet branchTys
  -- Not quite correct. Does not detect duplicate provided ctors
  when (provided /= required) $
    throwError BadCaseLabels
  for_ branches $ \ (c, k) -> do
    let branchTy = branchTys Map.! c
    checkCoValue k (ContK branchTy)

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
checkCompare (CmpEqCharK x y) = checkTmVar x CharK *> checkTmVar y CharK

checkStringOp :: StringOpK -> TC TypeK
checkStringOp (ConcatK x y) = checkTmVar x StringK *> checkTmVar y StringK *> pure StringK
checkStringOp (IndexK x y) = checkTmVar x StringK *> checkTmVar y IntK *> pure CharK
checkStringOp (LengthK x) = checkTmVar x StringK *> pure IntK

checkIntBinOp :: TmVar -> TmVar -> TC ()
checkIntBinOp x y = do
  checkTmVar x IntK
  checkTmVar y IntK

checkValue :: ValueK -> TypeK -> TC ()
checkValue NilK UnitK = pure ()
checkValue (PairK x y) (ProdK t s) = do
  checkTmVar x t
  checkTmVar y s
checkValue (RecordValK fs) (RecordK fs') = checkFields fs fs'
checkValue (IntValK _) IntK = pure ()
checkValue (BoolValK _) BoolK = pure ()
checkValue (StringValK _) StringK = pure ()
checkValue (CharValK _) CharK = pure ()
checkValue (CtorAppK c ts xs) t = do
  CtorType aas ss tcapp <- lookupCtor c
  sub <- makeSubst aas ts
  checkTmArgs xs (map (substTypeK sub) ss)
  equalTypes (fromTyConApp $ substTyConApp sub tcapp) t
checkValue WorldTokenK TokenK = pure ()
checkValue v t = throwError (BadValue v t)

checkFields :: [(FieldLabel, TmVar)] -> [(FieldLabel, TypeK)] -> TC ()
checkFields [] [] = pure ()
checkFields ((f, x):fs) ((f', t):fs') = do
  when (f' /= f) $
    throwError (LabelMismatch f' f)
  checkTmVar x t
  checkFields fs fs'
checkFields _ _ = throwError ArityMismatch

checkPrimIO :: PrimIO -> TC TypeK
checkPrimIO (PrimGetLine s) = do
  checkTmVar s TokenK
  pure StringK
checkPrimIO (PrimPutLine s x) = do
  checkTmVar s TokenK
  checkTmVar x StringK
  pure UnitK

instantiateTyConApp :: TyConApp -> TC (Map Ctor [TypeK])
instantiateTyConApp (TyConApp tc tys) = do
  DataDecl _ _ ctors <- lookupDataDecl tc
  ctorDefs <- for ctors $ \ (CtorDecl c params argTys) -> do
    sub <- makeSubst params tys
    pure (c, map (substTypeK sub) argTys)
  pure (Map.fromList ctorDefs)

makeSubst :: [(TyVar, KindK)] -> [TypeK] -> TC Subst
makeSubst params args = listSubst <$> go params args
  where
    go [] [] = pure []
    go ((aa, k) : aas) (t : ts) = checkType t k *> fmap ((aa, t) :) (go aas ts)
    go _ _ = throwError ArityMismatch

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

checkCoArgs :: [CoValueK] -> [CoTypeK] -> TC ()
checkCoArgs [] [] = pure ()
checkCoArgs (k:ks) (s:ss) = checkCoValue k s *> checkCoArgs ks ss
checkCoArgs _ _ = throwError ArityMismatch

checkCoValue :: CoValueK -> CoTypeK -> TC ()
checkCoValue (CoVarK k) s = checkCoVar k s
checkCoValue (ContValK cont) s = do
  s' <- inferContDef cont
  equalCoTypes s s'


-- | Check that a type has the given kind.
inferType :: TypeK -> TC KindK
inferType (TyVarOccK aa) = lookupTyVar aa
inferType (TyConOccK tc) = lookupTyCon tc
inferType (AllK aas ss) =
  withTyVars aas (traverse_ (\s -> checkCoType s StarK) ss) *>
  pure StarK
inferType (FunK ts ss) =
  traverse_ (\t -> checkType t StarK) ts *>
  traverse_ (\s -> checkCoType s StarK) ss *>
  pure StarK
inferType (ProdK t s) = checkType t StarK *> checkType s StarK *> pure StarK
-- Hmm. Check that field labels are unique?
inferType (RecordK fields) = traverse_ (\ (f, t) -> checkType t StarK) fields *> pure StarK
inferType UnitK = pure StarK
inferType IntK = pure StarK
inferType BoolK = pure StarK
inferType StringK = pure StarK
inferType CharK = pure StarK
inferType (TyAppK t s) =
  inferType t >>= \case
    KArrK k1 k2 -> checkType s k1 *> pure k2
    StarK -> throwError (CannotTyApp t)
inferType TokenK = pure StarK

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
