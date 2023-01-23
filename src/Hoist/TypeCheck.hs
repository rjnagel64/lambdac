
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
  , sigTyCons :: Map TyCon DataDecl
  }

-- | Represents the type of a closure, a code pointer with environment
-- @code(@aa+, { (l : s)+ }; S)@.
data ClosureDeclType = ClosureDeclType [(TyVar, Kind)] [(Id, Sort)] ClosureTele

-- | The typing context contains the type of each item in scope, plus the type
-- of the environment parameter.
data Context
  = Context {
    ctxPlaces :: Map Id Sort
  , ctxTypes :: Map TyVar Kind
  , ctxEnvFields :: [(Id, Sort)]
  }

-- | Ways in which a Hoist IR program can be invalid.
data TCError
  = TypeMismatch Sort Sort
  | KindMismatch Kind Kind
  | ArgumentCountMismatch
  | WrongClosureArg
  | LabelMismatch Id Id

  | NameNotInScope Id
  | TyVarNotInScope TyVar
  | TyConNotInScope TyCon
  | CodeNotInScope CodeLabel

  | DuplicateLabels [String]
  | BadValue
  | BadCtorApp
  | BadProjection Sort Projection
  | BadCase TyConApp [(Ctor, Name)]
  | BadCaseLabels
  | BadOpen Name Sort
  | BadTyApp

instance Show TCError where
  show (TypeMismatch expected actual) = unlines
    [ "type mismatch:"
    , "expected type: " ++ pprintSort expected
    , "actual type:   " ++ pprintSort actual
    ]
  show (KindMismatch expected actual) = unlines
    [ "kind mismatch:"
    , "expected kind: " ++ pprintKind expected
    , "actual kind:   " ++ pprintKind actual
    ]
  show ArgumentCountMismatch = "incorrect number of arguments to something"
  show (LabelMismatch expected actual) = unlines
    [ "incorrect field label:"
    , "expected label: " ++ show expected
    , "actual label:   " ++ show actual
    ]
  show WrongClosureArg = "incorrect sort of argument provided to closure (value vs. type)"
  show (NameNotInScope x) = "variable " ++ show x ++ " not in scope"
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


lookupName :: Name -> TC Sort
lookupName (LocalName x) = do
  ctx <- asks ctxPlaces
  case Map.lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInScope x
lookupName (EnvName x) = do
  ctx <- asks ctxEnvFields
  case lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInScope x

lookupTyVar :: TyVar -> TC Kind
lookupTyVar aa = do
  ctx <- asks ctxTypes
  case Map.lookup aa ctx of
    Just k -> pure k
    Nothing -> do
      throwError $ TyVarNotInScope aa

lookupTyCon :: TyCon -> TC DataDecl
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

equalSorts :: Sort -> Sort -> TC ()
equalSorts expected actual =
  when (expected /= actual) $
    throwError (TypeMismatch expected actual)

equalKinds :: Kind -> Kind -> TC ()
equalKinds expected actual =
  when (expected /= actual) $
    throwError (KindMismatch expected actual)

withPlace :: Place -> TC a -> TC a
withPlace (Place s x) m = do
  checkSort s Star
  local extend m
  where extend (Context places tys env) = Context (Map.insert x s places) tys env

withPlaces :: [Place] -> TC a -> TC a
withPlaces ps = foldr (.) id (map withPlace ps)

withTyVar :: TyVar -> Kind -> TC a -> TC a
withTyVar aa k m = local (\ (Context places tys env) -> Context places (Map.insert aa k tys) env) m

withTyVars :: [(TyVar, Kind)] -> TC a -> TC a
withTyVars aas = foldr (.) id (map (uncurry withTyVar) aas)



checkProgram :: Program -> Either TCError ()
checkProgram (Program ds e) = runTC $ do
  traverse_ checkDecl ds 
  checkEntryPoint e

checkDecl :: Decl -> TC ()
checkDecl (DeclData dd) = checkDataDecl dd
checkDecl (DeclCode cd) = checkCodeDecl cd

checkEntryPoint :: TermH -> TC ()
checkEntryPoint e = checkTerm e

dataDeclKind :: DataDecl -> Kind
dataDeclKind (DataDecl _ params _) = foldr (\ (_, k1) k2 -> KArr k1 k2) Star params

checkDataDecl :: DataDecl -> TC ()
checkDataDecl dd@(DataDecl tc params ctors) = do
  modify (\ (Signature clos tcs) -> Signature clos (Map.insert tc dd tcs))
  withTyVars params $ traverse_ checkCtorDecl ctors

checkCtorDecl :: CtorDecl -> TC ()
checkCtorDecl (CtorDecl _c args) = do
  checkUniqueLabels (map fst args)
  traverse_ (\ (_x, s) -> checkSort s Star) args

-- | Type-check a top-level code declaration and add it to the signature.
checkCodeDecl :: CodeDecl -> TC ()
checkCodeDecl decl@(CodeDecl cl (envp, envd) params body) = do
  -- Check the environment and parameters to populate the environment scope for
  -- the typing context
  (typarams, recordparam) <- checkEnvDecl envd
  local (\ (Context _ _ _) -> Context Map.empty (Map.fromList typarams) recordparam) $ do
    withParams params $ checkTerm body
  let tele = codeDeclTele decl
  let declTy = ClosureDeclType typarams recordparam tele
  modify (\ (Signature clos tcs) -> Signature (Map.insert cl declTy clos) tcs)

withParams :: [ClosureParam] -> TC a -> TC a
withParams [] m = m
withParams (PlaceParam p : params) m = withPlace p $ withParams params m
withParams (TypeParam aa k : params) m = withTyVar aa k $ withParams params m

-- Check that all field labels are disjoint, and that each field type is
-- well-formed.
checkEnvDecl :: EnvDecl -> TC ([(TyVar, Kind)], [(Id, Sort)])
checkEnvDecl (EnvDecl tys places) = do
  checkUniqueLabels [placeName p | p <- places]

  fields <- withTyVars tys $ for places $ \ (Place s x) -> do
    checkSort s Star
    pure (x, s)
  pure (tys, fields)

-- | Use a Map to count muliplicity of each label.
-- Report labels that appear more than once.
checkUniqueLabels :: (Ord a, Show a) => [a] -> TC ()
checkUniqueLabels ls = do
  let multiplicity = Map.fromListWith (+) [(l, 1 :: Int) | l <- ls]
  let duplicates = Map.keys $ Map.filter (> 1) multiplicity
  unless (null duplicates) $ throwError (DuplicateLabels (map show duplicates))

-- | Type-check a term, with the judgement @Σ; Γ |- e OK@.
checkTerm :: TermH -> TC ()
checkTerm (LetValH p v e) = do
  checkSort (placeSort p) Star
  checkValue v (placeSort p)
  withPlace p $ checkTerm e
checkTerm (LetPrimH p prim e) = do
  s <- checkPrimOp prim
  equalSorts (placeSort p) s
  withPlace p $ checkTerm e
checkTerm (LetProjectH p x proj e) = do
  s <- lookupName x
  case (s, proj) of
    (ProductH s' _, ProjectFst) -> equalSorts (placeSort p) s'
    (ProductH _ t', ProjectSnd) -> equalSorts (placeSort p) t'
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
checkTerm (CaseH x kind ks) = checkCase x kind ks
checkTerm (AllocClosure cs e) = do
  let binds = map closurePlace cs
  withPlaces binds $ do
    for_ cs $ \ (ClosureAlloc p c envPlace env) -> do
      ClosureDeclType typarams recordparam tele <- lookupCodeDecl c
      tele' <- checkEnvAlloc (ClosureDeclType typarams recordparam tele) env
      equalSorts (placeSort p) (ClosureH tele')
    checkTerm e

checkName :: Name -> Sort -> TC ()
checkName x s = do
  s' <- lookupName x
  equalSorts s s'

-- This should be
-- ClosureDeclType -> EnvAlloc -> TC ClosureTele, where the returned telescope
-- has been substituted with the envalloc's type arguments.
checkEnvAlloc :: ClosureDeclType -> EnvAlloc -> TC ClosureTele
checkEnvAlloc (ClosureDeclType typarams fields tele) (EnvAlloc tyargs valArgs) = do
  -- Subst envTyVars envTy for tyargs
  -- Use that to check { valArgs } against envTyFields
  -- Record equality: are fields required to be in same order?
  -- Probably??? Records are just labelled tuples, right???
  sub <- makeSubst typarams tyargs
  let fieldTys = map (\ (x, s) -> (x, substSort sub s)) fields
  checkFieldTys valArgs fieldTys

  pure (substTele sub tele)

-- TODO: Generalize checkFieldTys to checkRecordValue
checkFieldTys :: [(Id, Name)] -> [(Id, Sort)] -> TC ()
checkFieldTys [] [] = pure ()
checkFieldTys ((f', x) : fields) ((f, s) : fieldTys) = do
  when (f /= f') $
    throwError (LabelMismatch f f')
  checkName x s
  checkFieldTys fields fieldTys
checkFieldTys _ _ = throwError ArgumentCountMismatch

makeSubst :: [(TyVar, Kind)] -> [Sort] -> TC Subst
makeSubst params args = listSubst <$> go params args
  where
    go [] [] = pure []
    go ((aa, k) : aas) (t : ts) = checkSort t k *> fmap ((aa, t) :) (go aas ts)
    go _ _ = throwError ArgumentCountMismatch

-- | Check that an argument list matches a parameter telescope,
-- @Σ; Γ |- E : S@.
checkCallArgs :: [TeleEntry] -> [ClosureArg] -> TC ()
checkCallArgs [] [] = pure ()
checkCallArgs (ValueTele s : tele) (ValueArg x : args) = do
  checkName x s
  checkCallArgs tele args
checkCallArgs (ValueTele _ : _) (_ : _) = throwError WrongClosureArg
checkCallArgs (TypeTele aa k : tele) (TypeArg s : args) = do
  checkSort s k
  let ClosureTele tele' = substTele (singleSubst aa s) (ClosureTele tele)
  checkCallArgs tele' args
checkCallArgs (TypeTele _ _ : _) (_ : _) = throwError WrongClosureArg
checkCallArgs [] _ = throwError ArgumentCountMismatch
checkCallArgs (_ : _) [] = throwError ArgumentCountMismatch

-- | Check that a primitive operation has correct argument sorts, and yield its
-- return sort.
checkPrimOp :: PrimOp -> TC Sort
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
checkPrimOp (PrimConcatenate x y) = checkName x StringH *> checkName y StringH *> pure StringH
checkPrimOp (PrimStrlen x) = checkName x StringH *> pure IntegerH

-- | Check that a value has the given sort.
checkValue :: ValueH -> Sort -> TC ()
checkValue (IntH _) IntegerH = pure ()
checkValue (IntH _) _ = throwError BadValue
checkValue NilH UnitH = pure ()
checkValue NilH _ = throwError BadValue
checkValue (PairH x y) (ProductH s t) = do
  checkName x s
  checkName y t
checkValue (PairH _ _) _ = throwError BadValue
checkValue (StringValH _) StringH = pure ()
checkValue (StringValH _) _ = throwError BadValue
checkValue (CtorAppH capp) s = case asTyConApp s of
  Nothing -> throwError BadCtorApp
  Just tcapp -> checkCtorApp capp tcapp

checkCtorApp :: CtorAppH -> TyConApp -> TC ()
checkCtorApp (BoolH _) CaseBool = checkCtorArgs [] []
checkCtorApp _ CaseBool = throwError BadCtorApp 
checkCtorApp (InlH x) (CaseSum t _s) = checkCtorArgs [x] [t]
checkCtorApp (InrH y) (CaseSum _t s) = checkCtorArgs [y] [s]
checkCtorApp _ (CaseSum _ _) = throwError BadCtorApp
checkCtorApp (CtorApp c args) (TyConApp tc tys) = do
  -- TODO: Do this like in CPS.TypeCheck.checkCtorApp
  DataDecl _ params ctors <- lookupTyCon tc
  argTys <- case lookup c [(c', as) | CtorDecl c' as <- ctors] of
    Nothing -> throwError BadCtorApp
    Just as -> pure as
  let sub = listSubst (zip (map fst params) tys)
  checkCtorArgs args (map (substSort sub . snd) argTys)
checkCtorApp _ (TyConApp _ _) = throwError BadCtorApp

checkCtorArgs :: [Name] -> [Sort] -> TC ()
checkCtorArgs [] [] = pure ()
checkCtorArgs (x : xs) (t : ts) = checkName x t *> checkCtorArgs xs ts
checkCtorArgs _ _ = throwError ArgumentCountMismatch

-- I think I need something like DataDesc here.
-- * Check scrutinee has same type as the TyConApp
-- * Check coverage of branches?
-- * Lookup ctor, use that to check type of continuation
checkCase :: Name -> TyConApp -> [(Ctor, Name)] -> TC ()
checkCase x tcapp branches = do
  checkName x (fromTyConApp tcapp)
  branchTys <- instantiateTyConApp tcapp
  checkBranches branches branchTys

checkBranches :: [(Ctor, Name)] -> Map Ctor [TeleEntry] -> TC ()
checkBranches branches branchTys = do
  let provided = Set.fromList (map fst branches)
  let required = Map.keysSet branchTys
  when (provided /= required) $
    throwError BadCaseLabels
  for_ branches $ \ (c, k) -> do
    let branchTy = branchTys Map.! c
    checkName k (ClosureH (ClosureTele branchTy))

instantiateTyConApp :: TyConApp -> TC (Map Ctor [TeleEntry])
instantiateTyConApp CaseBool =
  pure $ Map.fromList [(Ctor "false", []), (Ctor "true", [])]
instantiateTyConApp (CaseSum t s) =
  pure $ Map.fromList [(Ctor "inl", [ValueTele t]), (Ctor "inr", [ValueTele s])]
instantiateTyConApp (TyConApp tc tys) = do
  DataDecl _ params ctors <- lookupTyCon tc
  sub <- makeSubst params tys
  let cs = Map.fromList [(c, map (ValueTele . substSort sub . snd) argTys) | CtorDecl c argTys <- ctors]
  pure cs

-- | Check that a sort is well-formed w.r.t. the context
inferSort :: Sort -> TC Kind
inferSort (AllocH aa) = lookupTyVar aa
inferSort (TyConH tc) = dataDeclKind <$> lookupTyCon tc
inferSort (TyAppH t s) = do
  inferSort t >>= \case
    KArr k1 k2 -> checkSort s k1 *> pure k2
    Star -> throwError BadTyApp
inferSort UnitH = pure Star
inferSort IntegerH = pure Star
inferSort BooleanH = pure Star
inferSort StringH = pure Star
inferSort (ProductH t s) = checkSort t Star *> checkSort s Star *> pure Star
inferSort (SumH t s) = checkSort t Star *> checkSort s Star *> pure Star
inferSort (ClosureH tele) = checkTele tele *> pure Star

checkSort :: Sort -> Kind -> TC ()
checkSort s k = inferSort s >>= equalKinds k

-- | Check that a telescope is well-formed w.r.t the context.
-- @Γ |- S@
checkTele :: ClosureTele -> TC ()
checkTele (ClosureTele ss) = go ss
  where
    go [] = pure ()
    go (ValueTele s : ss') = checkSort s Star *> go ss'
    go (TypeTele aa k : ss') = withTyVar aa k $ go ss'

