
module Hoist.TypeCheck (checkProgram, TCError(..)) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set

import Data.Foldable (traverse_, for_)
import Data.Traversable (for)
import Data.List (intercalate)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Hoist.IR


newtype TC a = TC { getTC :: StateT Signature (ReaderT Context (Except TCError)) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadError TCError TC
deriving newtype instance MonadReader Context TC
deriving newtype instance MonadState Signature TC

-- | The signature stores information about top-level declarations.
data Signature
  = Signature {
    sigClosures :: Map CodeLabel ClosureDeclType
  , sigTyCons :: Map TyCon (Kind, [CtorDecl])
  }

-- | Represents the type of a closure, a code pointer with environment
-- @code(@aa+, { (l : s)+ }; S)@.
data ClosureDeclType = ClosureDeclType [(TyVar, Kind)] [(FieldLabel, Type)] ClosureTele

-- | The typing context contains the type of each item in scope, plus the type
-- of the environment parameter.
data Context
  = Context {
    ctxPlaces :: Map Id Type
  , ctxTypes :: Map TyVar Kind
  , ctxEnvFields :: [(FieldLabel, Type)]
  }

-- | Ways in which a Hoist IR program can be invalid.
data TCError
  = TypeMismatch Type Type
  | KindMismatch Kind Kind
  | ArgumentCountMismatch
  | WrongClosureArg
  -- | LabelMismatch Id Id
  | FieldLabelMismatch FieldLabel FieldLabel

  | NameNotInScope Id
  | EnvNameNotInScope FieldLabel
  | TyVarNotInScope TyVar
  | TyConNotInScope TyCon
  | CodeNotInScope CodeLabel

  | DuplicateLabels [String]
  | BadValue
  | BadCtorApp
  | BadProjection Type Projection
  | BadCase TyConApp [(Ctor, Name)]
  | BadCaseLabels
  | BadOpen Name Type
  | BadTyApp

instance Show TCError where
  show (TypeMismatch expected actual) = unlines
    [ "type mismatch:"
    , "expected type: " ++ pprintType expected
    , "actual type:   " ++ pprintType actual
    ]
  show (KindMismatch expected actual) = unlines
    [ "kind mismatch:"
    , "expected kind: " ++ pprintKind expected
    , "actual kind:   " ++ pprintKind actual
    ]
  show ArgumentCountMismatch = "incorrect number of arguments to something"
  -- show (LabelMismatch expected actual) = unlines
  --   [ "incorrect field label:"
  --   , "expected label: " ++ show expected
  --   , "actual label:   " ++ show actual
  --   ]
  show (FieldLabelMismatch expected actual) = unlines
    [ "incorrect field label:"
    , "expected label: " ++ show expected
    , "actual label:   " ++ show actual
    ]
  show WrongClosureArg = "incorrect sort of argument provided to closure (value vs. type)"
  show (NameNotInScope x) = "variable " ++ show x ++ " not in local scope"
  show (EnvNameNotInScope x) = "variable " ++ show x ++ " not in environment"
  show (TyVarNotInScope aa) = "type variable " ++ show aa ++ " not in scope"
  show (TyConNotInScope tc) = "type constructor " ++ show tc ++ " not in scope"
  show (CodeNotInScope c) = "code label " ++ show c ++ " not in scope"
  show (DuplicateLabels ls) = "duplicate labels: [" ++ intercalate ", " ls ++ "]"
  show BadValue = "invalid value"
  show BadCtorApp = "invalid constructor application"
  show (BadProjection _ _) = "cannot project that field"
  show (BadCase _ _) = "invalid case analysis"
  show BadCaseLabels = "case labels incorrect"
  show (BadOpen _ _) = "invalid closure invocation"
  show BadTyApp = "bad type-level application"

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT emptyContext . flip evalStateT emptySignature . getTC
  where
    emptyContext = Context { ctxPlaces = Map.empty, ctxTypes = Map.empty, ctxEnvFields = [] }
    emptySignature = Signature { sigClosures = Map.empty, sigTyCons = Map.empty }


lookupName :: Name -> TC Type
lookupName (LocalName x) = do
  ctx <- asks ctxPlaces
  case Map.lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInScope x
lookupName (EnvName x) = do
  ctx <- asks ctxEnvFields
  case lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ EnvNameNotInScope x

lookupTyVar :: TyVar -> TC Kind
lookupTyVar aa = do
  ctx <- asks ctxTypes
  case Map.lookup aa ctx of
    Just k -> pure k
    Nothing -> do
      throwError $ TyVarNotInScope aa

lookupTyCon :: TyCon -> TC (Kind, [CtorDecl])
lookupTyCon tc = do
  ctx <- gets sigTyCons
  case Map.lookup tc ctx of
    Just dd -> pure dd
    Nothing -> throwError $ TyConNotInScope tc

lookupCodeDecl :: CodeLabel -> TC ClosureDeclType
lookupCodeDecl c = do
  sig <- gets sigClosures
  case Map.lookup c sig of
    Just t -> pure t
    Nothing -> throwError $ CodeNotInScope c

equalType :: Type -> Type -> TC ()
equalType expected actual =
  when (expected /= actual) $
    throwError (TypeMismatch expected actual)

equalKinds :: Kind -> Kind -> TC ()
equalKinds expected actual =
  when (expected /= actual) $
    throwError (KindMismatch expected actual)

withPlace :: Place -> TC a -> TC a
withPlace (Place s x) m = do
  checkType s Star
  local extend m
  where extend (Context places tys env) = Context (Map.insert x s places) tys env

withPlaces :: [Place] -> TC a -> TC a
withPlaces ps = foldr (.) id (map withPlace ps)

withTyVar :: TyVar -> Kind -> TC a -> TC a
withTyVar aa k m = local (\ (Context places tys env) -> Context places (Map.insert aa k tys) env) m

withTyVars :: [(TyVar, Kind)] -> TC a -> TC a
withTyVars aas = foldr (.) id (map (uncurry withTyVar) aas)

withParams :: [ClosureParam] -> TC a -> TC a
withParams [] m = m
withParams (PlaceParam p : params) m = withPlace p $ withParams params m
withParams (TypeParam aa k : params) m = withTyVar aa k $ withParams params m


-- | Construct a well-kinded substitution by zipping a list of type parameters
-- with a list of argument types.
parameterSubst :: [(TyVar, Kind)] -> [Type] -> TC Subst
parameterSubst params args = listSubst <$> go params args
  where
    go [] [] = pure []
    go ((aa, k) : aas) (t : ts) = checkType t k *> fmap ((aa, t) :) (go aas ts)
    go _ _ = throwError ArgumentCountMismatch

-- | Use a Map to count muliplicity of each label.
-- Report labels that appear more than once.
checkUniqueLabels :: (Ord a, Show a) => [a] -> TC ()
checkUniqueLabels ls = do
  let multiplicity = Map.fromListWith (+) [(l, 1 :: Int) | l <- ls]
  let duplicates = Map.keys $ Map.filter (> 1) multiplicity
  unless (null duplicates) $ throwError (DuplicateLabels (map show duplicates))



checkProgram :: Program -> Either TCError ()
checkProgram (Program ds e) = runTC $ do
  traverse_ checkDecl ds 
  checkEntryPoint e

checkDecl :: Decl -> TC ()
checkDecl (DeclData dd) = checkDataDecl dd
checkDecl (DeclCode cd) = checkCodeDecl cd

checkEntryPoint :: TermH -> TC ()
checkEntryPoint e = checkTerm e

checkDataDecl :: DataDecl -> TC ()
checkDataDecl (DataDecl tc kind ctors) = do
  modify (\ (Signature clos tcs) -> Signature clos (Map.insert tc (kind, ctors) tcs))
  traverse_ checkCtorDecl ctors

checkCtorDecl :: CtorDecl -> TC ()
checkCtorDecl (CtorDecl _c tys args) = do
  checkUniqueLabels (map fst args)
  withTyVars tys $ traverse_ (\ (_x, s) -> checkType s Star) args

-- | Type-check a top-level code declaration and add it to the signature.
checkCodeDecl :: CodeDecl -> TC ()
checkCodeDecl decl@(CodeDecl cl (_envp, envd) params body) = do
  -- Check the environment and parameters to populate the environment scope for
  -- the typing context
  withEnvDecl envd $ 
    withParams params $
      checkTerm body
  let declTy = codeDeclType decl
  modify (\ (Signature clos tcs) -> Signature (Map.insert cl declTy clos) tcs)

-- | Check that all field labels are disjoint, and that each field type is
-- well-formed.
withEnvDecl :: EnvDecl -> TC a -> TC a
withEnvDecl (EnvDecl tys fields) m = do
  checkUniqueLabels [x | (x, _) <- fields]
  withTyVars tys $ traverse_ (\ (_x, s) -> checkType s Star) fields
  let extend (Context _ _ _) = Context Map.empty (Map.fromList tys) fields
  local extend $ m

codeDeclType :: CodeDecl -> ClosureDeclType
codeDeclType (CodeDecl _cl (_envp, (EnvDecl typarams recordparam)) params _body) =
  ClosureDeclType typarams recordparam (ClosureTele (map f params))
  where
    f (PlaceParam p) = ValueTele (placeType p)
    f (TypeParam aa k) = TypeTele aa k


-- | Type-check a term, with the judgement @Σ; Γ |- e OK@.
checkTerm :: TermH -> TC ()
checkTerm (LetValH p v e) = do
  checkType (placeType p) Star
  checkValue v (placeType p)
  withPlace p $ checkTerm e
checkTerm (LetPrimH p prim e) = do
  s <- checkPrimOp prim
  equalType (placeType p) s
  withPlace p $ checkTerm e
checkTerm (LetBindH p1 p2 prim e) = do
  s <- checkPrimIO prim
  equalType (placeType p1) TokenH
  equalType (placeType p2) s
  withPlace p1 $ withPlace p2 $ checkTerm e
checkTerm (LetProjectH p x proj e) = do
  s <- lookupName x
  case (s, proj) of
    (ProductH s' _, ProjectFst) -> equalType (placeType p) s'
    (ProductH _ t', ProjectSnd) -> equalType (placeType p) t'
    (RecordH fs, ProjectField f) -> case lookup f fs of
      Nothing -> throwError (BadProjection s proj)
      Just s' -> equalType (placeType p) s'
    (_, _) -> throwError (BadProjection s proj)
  withPlace p $ checkTerm e
checkTerm (HaltH s x) = do
  checkName x s
checkTerm (OpenH f args) = do
  -- Infer type of closure
  ClosureTele tele <- lookupName f >>= \case
    ClosureH tele -> pure tele
    s -> throwError (BadOpen f s)
  -- Check that args match closure telescope
  checkCallArgs tele args
checkTerm (IfH x k1 k2) = do
  checkName x BooleanH
  checkName k1 (ClosureH (ClosureTele []))
  checkName k2 (ClosureH (ClosureTele []))
checkTerm (CaseH x kind ks) = checkCase x kind ks
checkTerm (AllocClosure cs e) = do
  let binds = map closurePlace cs
  withPlaces binds $ do
    for_ cs $ \ (ClosureAlloc p c envPlace env) -> do
      ClosureDeclType typarams recordparam tele <- lookupCodeDecl c
      tele' <- checkEnvAlloc (ClosureDeclType typarams recordparam tele) env
      equalType (placeType p) (ClosureH tele')
    checkTerm e

checkName :: Name -> Type -> TC ()
checkName x s = do
  s' <- lookupName x
  equalType s s'

checkEnvAlloc :: ClosureDeclType -> EnvAlloc -> TC ClosureTele
checkEnvAlloc (ClosureDeclType typarams fields tele) (EnvAlloc tyargs valArgs) = do
  -- Subst envTyVars envTy for tyargs
  -- Use that to check { valArgs } against envTyFields
  -- Record equality: are fields required to be in same order?
  -- Probably??? Records are just labelled tuples, right???
  sub <- parameterSubst typarams tyargs
  let fieldTys = map (\ (x, s) -> (x, substType sub s)) fields
  checkFieldTys valArgs fieldTys

  pure (substTele sub tele)

-- Note: I eventually might want to generalize checkFieldTys to
-- checkRecordValue, as a closure environment is basically just a record.
checkFieldTys :: [(FieldLabel, Name)] -> [(FieldLabel, Type)] -> TC ()
checkFieldTys [] [] = pure ()
checkFieldTys ((f', x) : fields) ((f, s) : fieldTys) = do
  when (f /= f') $
    throwError (FieldLabelMismatch f f')
  checkName x s
  checkFieldTys fields fieldTys
checkFieldTys _ _ = throwError ArgumentCountMismatch

-- Note: checkRecordValue is nearly identical to checkFieldTys. The only
-- difference is that one uses FieldLabel, but the other uses Id.
--
-- An environment type is *almost* like a record type, but not quite.
-- Specifically, all fields of an environment are statically known, but record
-- values currently have to look up their field offsets at runtime.
-- I hope to mitigate this in the future by making record values more
-- efficient, but I can't yet.
checkRecordValue :: [(FieldLabel, Name)] -> [(FieldLabel, Type)] -> TC ()
checkRecordValue [] [] = pure ()
checkRecordValue ((f', x) : fields) ((f, s) : fieldTys) = do
  when (f /= f') $
    throwError (FieldLabelMismatch f f')
  checkName x s
  checkRecordValue fields fieldTys
checkRecordValue _ _ = throwError ArgumentCountMismatch

-- | Check that an argument list matches a parameter telescope,
-- @Σ; Γ |- E : S@.
checkCallArgs :: [TeleEntry] -> [ClosureArg] -> TC ()
checkCallArgs [] [] = pure ()
checkCallArgs (ValueTele s : tele) (ValueArg x : args) = do
  checkName x s
  checkCallArgs tele args
checkCallArgs (ValueTele _ : _) (_ : _) = throwError WrongClosureArg
checkCallArgs (TypeTele aa k : tele) (TypeArg s : args) = do
  checkType s k
  let ClosureTele tele' = substTele (singleSubst aa s) (ClosureTele tele)
  checkCallArgs tele' args
checkCallArgs (TypeTele _ _ : _) (_ : _) = throwError WrongClosureArg
checkCallArgs [] _ = throwError ArgumentCountMismatch
checkCallArgs (_ : _) [] = throwError ArgumentCountMismatch

-- | Check that a primitive operation has correct argument sorts, and yield its
-- return sort.
checkPrimOp :: PrimOp -> TC Type
checkPrimOp (PrimAddInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure IntegerH
checkPrimOp (PrimSubInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure IntegerH
checkPrimOp (PrimMulInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure IntegerH
checkPrimOp (PrimNegInt64 x) = checkName x IntegerH *> pure IntegerH
checkPrimOp (PrimEqInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure BooleanH
checkPrimOp (PrimNeInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure BooleanH
checkPrimOp (PrimLtInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure BooleanH
checkPrimOp (PrimLeInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure BooleanH
checkPrimOp (PrimGtInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure BooleanH
checkPrimOp (PrimGeInt64 x y) = checkName x IntegerH *> checkName y IntegerH *> pure BooleanH
checkPrimOp (PrimEqChar x y) = checkName x CharH *> checkName y CharH *> pure BooleanH
checkPrimOp (PrimConcatenate x y) = checkName x StringH *> checkName y StringH *> pure StringH
checkPrimOp (PrimStrlen x) = checkName x StringH *> pure IntegerH
checkPrimOp (PrimIndexStr x y) = checkName x StringH *> checkName y IntegerH *> pure CharH

-- | Check an I/O primitive operation, and compute its return sort.
checkPrimIO :: PrimIO -> TC Type
checkPrimIO (PrimGetLine x) = checkName x TokenH *> pure StringH
checkPrimIO (PrimPutLine x y) = checkName x TokenH *> checkName y StringH *> pure UnitH

-- | Check that a value has the given sort.
checkValue :: ValueH -> Type -> TC ()
checkValue (IntH _) IntegerH = pure ()
checkValue (IntH _) _ = throwError BadValue
checkValue (BoolH _) BooleanH = pure ()
checkValue (BoolH _) _ = throwError BadValue
checkValue NilH UnitH = pure ()
checkValue NilH _ = throwError BadValue
checkValue (PairH x y) (ProductH s t) = do
  checkName x s
  checkName y t
checkValue (PairH _ _) _ = throwError BadValue
checkValue (StringValH _) StringH = pure ()
checkValue (StringValH _) _ = throwError BadValue
checkValue (CharValH _) CharH = pure ()
checkValue (CharValH _) _ = throwError BadValue
checkValue WorldToken TokenH = pure ()
checkValue WorldToken _ = throwError BadValue
checkValue (RecordValH fieldVals) (RecordH fieldTys) = checkRecordValue fieldVals fieldTys
checkValue (RecordValH _) _ = throwError BadValue
checkValue (CtorAppH c tyargs args) s = do
  tcapp <- case asTyConApp s of
    Nothing -> throwError BadCtorApp
    Just tcapp -> pure tcapp
  ctors <- instantiateTyConApp tcapp
  case Map.lookup c ctors of
    Nothing -> throwError BadCtorApp
    Just argTys -> checkCtorArgs args argTys

-- | Check a constructor's argument list against the constructors type
-- signature.
--
-- Right now, constructors only have value arguments. However, in the future I
-- may implement existentially-quantified ADTs, which would additionally have
-- type arguments.
checkCtorArgs :: [Name] -> [TeleEntry] -> TC ()
checkCtorArgs [] [] = pure ()
checkCtorArgs (x : xs) (ValueTele t : ts) = checkName x t *> checkCtorArgs xs ts
checkCtorArgs (_ : _) (TypeTele _ _ : _) = throwError BadCtorApp -- no type arguments for ctors yet.
checkCtorArgs _ _ = throwError ArgumentCountMismatch

-- | Check that a case analysis is well-formed.
checkCase :: Name -> TyConApp -> [(Ctor, Name)] -> TC ()
checkCase x tcapp branches = do
  checkName x (fromTyConApp tcapp)
  branchTys <- instantiateTyConApp tcapp
  checkBranches branches branchTys

-- | Check that a set of case branches covers all the required constructors,
-- and check that each branch has the correct type.
checkBranches :: [(Ctor, Name)] -> Map Ctor [TeleEntry] -> TC ()
checkBranches branches branchTys = do
  let provided = Set.fromList (map fst branches)
  let required = Map.keysSet branchTys
  when (provided /= required) $
    throwError BadCaseLabels
  for_ branches $ \ (c, k) -> do
    let branchTy = branchTys Map.! c
    checkName k (ClosureH (ClosureTele branchTy))

-- | Given the application of a type constructor to a list of arguments,
-- compute a mapping from that type constructor's data constructors to the
-- instantiated type of that constructor.
instantiateTyConApp :: TyConApp -> TC (Map Ctor [TeleEntry])
instantiateTyConApp (TyConApp tc tys) = do
  ctors <- snd <$> lookupTyCon tc
  cs <- fmap Map.fromList $ for ctors $ \ (CtorDecl c typarams argTys) -> do
    sub <- parameterSubst typarams tys
    pure (c, map (ValueTele . substType sub . snd) argTys)
  pure cs

-- | Check that a sort is well-formed w.r.t. the context
inferType :: Type -> TC Kind
inferType (AllocH aa) = lookupTyVar aa
inferType (TyConH tc) = fst <$> lookupTyCon tc
inferType (TyAppH t s) = do
  inferType t >>= \case
    KArr k1 k2 -> checkType s k1 *> pure k2
    Star -> throwError BadTyApp
inferType UnitH = pure Star
inferType IntegerH = pure Star
inferType BooleanH = pure Star
inferType StringH = pure Star
inferType CharH = pure Star
inferType TokenH = pure Star
inferType (ProductH t s) = checkType t Star *> checkType s Star *> pure Star
inferType (RecordH fs) = traverse_ (\ (f, t) -> checkType t Star) fs *> pure Star
inferType (ClosureH tele) = checkTele tele *> pure Star

-- | Check that a sort has the specified kind.
checkType :: Type -> Kind -> TC ()
checkType s k = inferType s >>= equalKinds k

-- | Check that a telescope is well-formed w.r.t the context.
-- @Γ |- S@
checkTele :: ClosureTele -> TC ()
checkTele (ClosureTele ss) = go ss
  where
    go [] = pure ()
    go (ValueTele s : ss') = checkType s Star *> go ss'
    go (TypeTele aa k : ss') = withTyVar aa k $ go ss'

