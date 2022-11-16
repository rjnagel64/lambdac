
module Hoist.TypeCheck (checkProgram, runTC, TCError(..)) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Foldable (traverse_, for_)
import Data.Traversable (for)

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

-- | The signature stores information about top-level declarations. Currently,
-- this only includes code declarations.
data Signature = Signature { sigClosures :: Map ClosureName ClosureDeclType }

-- | Represents the type of a closure, a code pointer with environment
-- @code[aa+](t; S)@.
data ClosureDeclType = ClosureDeclType [TyVar] EnvType ClosureTele

-- | Represents the type of a closure environment, @{(m : info t)+; (l : s)+}@.
data EnvType = EnvType { envTypeInfos :: [(Id, Sort)], envTypeFields :: [(Id, Sort)] }

-- | The typing context is split into two scopes: local information and
-- environment information.
data Context = Context { ctxLocals :: Locals, ctxEnv :: EnvType }

-- | The local scope contains information about each identifier in the context,
-- except for the closure environment.
-- Values record their sort, @x : t@.
-- Type variables record their presence, @a : type@.
-- Info variables record the sort they describe, @i : info t@.
data Locals = Locals { localPlaces :: Map Id Sort, localTypes :: Set Id, localInfos :: Map Id Sort }

-- | Ways in which a Hoist IR program can be invalid.
data TCError
  = TypeMismatch Sort Sort
  | NameNotInLocals Id
  | TyVarNotInLocals TyVar
  | ClosureNotInLocals ClosureName
  | InfoNotInLocals Id
  | NotImplemented String
  | IncorrectInfo
  | BadValue
  | BadProjection Sort Projection
  | BadCase CaseKind [Name]
  | BadClosurePlace Id Sort
  | BadOpen Name Sort
  | WrongClosureArg
  | DuplicateLabels [String]

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT emptyContext . flip evalStateT emptySignature . getTC
  where
    emptyContext = Context { ctxLocals = emptyLocals, ctxEnv = emptyEnv }
    emptyEnv = EnvType { envTypeInfos = [], envTypeFields = [] }


emptyLocals :: Locals
emptyLocals = Locals Map.empty Set.empty Map.empty

bindPlace :: Place -> Locals -> Locals
bindPlace (Place s x) (Locals places tys infos) = Locals (Map.insert x s places) tys infos

-- TODO: bindInfo is poorly named
bindInfo :: InfoPlace -> Locals -> Locals
bindInfo (InfoPlace aa) (Locals places tys infos) = Locals places (Set.insert aa tys) infos

emptySignature :: Signature
emptySignature = Signature { sigClosures = Map.empty }

declareClosure :: ClosureName -> ClosureDeclType -> Signature -> Signature
declareClosure cl ty (Signature clos) = Signature (Map.insert cl ty clos)


lookupName :: Name -> TC Sort
lookupName (LocalName x) = do
  ctx <- asks (localPlaces . ctxLocals)
  case Map.lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInLocals x
lookupName (EnvName x) = do
  ctx <- asks (envTypeFields . ctxEnv)
  case lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInLocals x

lookupTyVar :: TyVar -> TC ()
lookupTyVar (TyVar aa) = do
  let aa' = Id aa
  ctx <- asks (localTypes . ctxLocals)
  case Set.member aa' ctx of
    True -> pure ()
    False -> throwError $ TyVarNotInLocals (TyVar aa)

lookupCodeDecl :: ClosureName -> TC ClosureDeclType
lookupCodeDecl c = do
  sig <- gets sigClosures
  case Map.lookup c sig of
    Just t -> pure t
    Nothing -> throwError $ ClosureNotInLocals c

equalSorts :: Sort -> Sort -> TC ()
equalSorts expected actual =
  when (expected /= actual) $
    throwError (TypeMismatch expected actual)

equalTeles :: ClosureTele -> ClosureTele -> TC ()
equalTeles expected actual = when (expected /= actual) $
  throwError (NotImplemented "equalTeles")

withPlace :: Place -> TC a -> TC a
withPlace p m = do
  checkSort (placeSort p)
  local extend m
  where extend (Context locals env) = Context (bindPlace p locals) env

withPlaces :: [Place] -> TC a -> TC a
withPlaces ps = foldr (.) id (map withPlace ps)

withInfo :: InfoPlace -> TC a -> TC a
withInfo i m = local extend m
  where extend (Context locals env) = Context (bindInfo i locals) env



checkName :: Name -> Sort -> TC ()
checkName x s = do
  s' <- lookupName x
  equalSorts s s'


checkProgram :: [ClosureDecl] -> TermH -> TC ()
checkProgram cs e = traverse_ checkClosure cs *> checkEntryPoint e

checkEntryPoint :: TermH -> TC ()
checkEntryPoint e = checkTerm e

-- | Type-check a top-level code declaration and add it to the signature.
checkClosure :: ClosureDecl -> TC ()
checkClosure (ClosureDecl cl (envp, envd) params body) = do
  -- Check the environment and parameters to populate the environment scope for
  -- the typing context
  envTy <- checkEnv envd
  -- Check that the parameter list is well-formed, and extract the initial
  -- contents of the local scope for the typing context.
  localScope <- checkParams params
  -- Use the parameter list and environment to type-check the closure body.
  local (\_ -> Context localScope envTy) $ checkTerm body
  -- Extend the signature with the new closure declaration.
  let
    -- Compute a telescope from a parameter list.
    -- Note how the muddled identifier sorts are messy here.
    mkParam (PlaceParam p) = ValueTele (placeSort p)
    mkParam (TypeParam (InfoPlace (Id aa))) = TypeTele (TyVar aa)
    tele = ClosureTele (map mkParam params)
  let declTy = ClosureDeclType [] envTy tele
  modify (declareClosure cl declTy)

checkEnv :: EnvDecl -> TC EnvType
-- Check that all (info/field) labels are disjoint, and that each field type is
-- well-formed.
checkEnv (EnvDecl tys places) = do
  checkUniqueLabels [aa | InfoPlace aa <- tys]
  checkUniqueLabels [placeName p | p <- places]

  infos <- for tys $ \ (InfoPlace (Id aa)) -> do
    -- Once InfoPlace is replaced by InfoPlace2, these two lines can go away.
    let infoLabel = Id aa
    let infoSort = AllocH (TyVar aa)
    checkSort infoSort
    pure (infoLabel, infoSort)
  fields <- for places $ \ (Place s x) -> do
    checkSort s
    pure (x, s)
  pure (EnvType infos fields)

-- | Use a Map to count muliplicity of each label.
-- Report labels that appear more than once.
checkUniqueLabels :: (Ord a, Show a) => [a] -> TC ()
checkUniqueLabels ls = do
  let multiplicity = Map.fromListWith (+) [(l, 1 :: Int) | l <- ls]
  let duplicates = Map.keys $ Map.filter (> 1) multiplicity
  if null duplicates then
    pure ()
  else
    throwError (DuplicateLabels (map show duplicates))

-- | Closure parameters form a telescope, because info bindings bring type
-- variables into scope for subsequent bindings.
checkParams :: [ClosureParam] -> TC Locals
checkParams [] = pure emptyLocals
checkParams (PlaceParam p : params) = withPlace p $ fmap (bindPlace p) (checkParams params)
checkParams (TypeParam i : params) = withInfo i $ fmap (bindInfo i) (checkParams params)

-- | Type-check a term, with the judgement @Σ; Γ |- e OK@.
checkTerm :: TermH -> TC ()
checkTerm (LetValH p v e) = do
  checkSort (placeSort p)
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
checkTerm (HaltH s x i) = do
  checkName x s
  checkInfo i s
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
      ClosureDeclType aas envTy tele <- lookupCodeDecl c
      -- instantiate aas (not yet present in Hoist)
      -- _
      -- check envTy
      checkEnvAlloc env envTy
      tele' <- case placeSort p of
        ClosureH tele' -> pure tele'
        s -> throwError (BadClosurePlace (placeName p) s)
      equalTeles tele' tele
    checkTerm e

checkEnvAlloc :: EnvAlloc -> EnvType -> TC ()
checkEnvAlloc env envTy = throwError (NotImplemented "checkEnvAlloc")

-- | Check that an argument list matches a parameter telescope,
-- @Σ; Γ |- E : S@.
checkCallArgs :: [TeleEntry] -> [ClosureArg] -> TC ()
checkCallArgs [] [] = pure ()
checkCallArgs (ValueTele s : tele) (ValueArg x : args) = do
  checkName x s
  checkCallArgs tele args
checkCallArgs (ValueTele _ : _) (_ : args) = throwError WrongClosureArg
-- checkCallArgs (TypeTele aa : tele) (TypeArg i : args) = do
--   checkSort s
--   -- Aargh, this TypeArg passes an 'Info', not a Sort
--   -- It's another example of the type param/type+info/info muddle
--   let tele' = _
--   checkCallArgs tele' args
-- Cases for TypeTele TypeArg and cases for ValueTele OpaqueArg
checkCallArgs tele args = do
  throwError (NotImplemented "checkCallArgs")

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

-- | Check that a value has the given sort.
checkValue :: ValueH -> Sort -> TC ()
checkValue (IntH _) IntegerH = pure ()
checkValue (IntH _) _ = throwError BadValue
checkValue (BoolH _) BooleanH = pure ()
checkValue (BoolH _) _ = throwError BadValue
checkValue NilH UnitH = pure ()
checkValue NilH _ = throwError BadValue
checkValue (InlH i x) SumH = do
  s <- lookupName x
  checkInfo i s
checkValue (InlH _ _) _ = throwError BadValue
checkValue (InrH i x) SumH = do
  s <- lookupName x
  checkInfo i s
checkValue (InrH _ _) _ = throwError BadValue
checkValue (PairH i j x y) (ProductH s t) = do
  s' <- lookupName x
  t' <- lookupName y
  equalSorts s s'
  equalSorts t t'
  checkInfo i s'
  checkInfo j t'
checkValue (PairH _ _ _ _) _ = throwError BadValue
checkValue ListNilH (ListH _) = pure ()
checkValue ListNilH _ = throwError BadValue
checkValue (ListConsH i x xs) (ListH t) = do
  checkInfo i t
  checkName x t
  checkName xs (ListH t) 
checkValue (ListConsH _ _ _) _ = throwError BadValue

checkCase :: Name -> CaseKind -> [Name] -> TC ()
checkCase x CaseBool [kf, kt] = do
  checkName x BooleanH
  checkName kf (ClosureH (ClosureTele []))
  checkName kt (ClosureH (ClosureTele []))
checkCase x (CaseSum a b) [kl, kr] = do
  checkName x SumH
  checkName kl (ClosureH (ClosureTele [ValueTele a]))
  checkName kr (ClosureH (ClosureTele [ValueTele b]))
checkCase x (CaseList a) [kn, kc] = do
  checkName x (ListH a)
  checkName kn (ClosureH (ClosureTele []))
  checkName kc (ClosureH (ClosureTele [ValueTele a, ValueTele (ListH a)]))
checkCase _ kind ks = throwError (BadCase kind ks)

-- | Check that a sort is well-formed w.r.t. the context
checkSort :: Sort -> TC ()
checkSort (AllocH aa) = lookupTyVar aa
checkSort UnitH = pure ()
checkSort IntegerH = pure ()
checkSort BooleanH = pure ()
checkSort SumH = pure ()
checkSort (ProductH t s) = checkSort t *> checkSort s
checkSort (ListH t) = checkSort t
checkSort (ClosureH tele) = checkTele tele

-- | Check that a telescope is well-formed w.r.t the context.
-- @Γ |- S@
checkTele :: ClosureTele -> TC ()
checkTele (ClosureTele ss) = go ss
  where
    go [] = pure ()
    go (ValueTele s : ss') = checkSort s *> go ss'
    go (TypeTele (TyVar aa) : ss') = withInfo (InfoPlace (Id aa)) $ go ss'

-- | Given info @i@ and sort @s@, check that @Γ |- i : info s@.
checkInfo :: Info -> Sort -> TC ()
checkInfo (LocalInfo i) s = do
  infos <- asks (localInfos . ctxLocals)
  case Map.lookup i infos of
    Nothing -> throwError (InfoNotInLocals i)
    Just s' -> equalSorts s s'
checkInfo (EnvInfo i) s = do
  infos <- asks (envTypeInfos . ctxEnv)
  case lookup i infos of
    Nothing -> throwError (InfoNotInLocals i)
    Just s' -> equalSorts s s'
checkInfo Int64Info IntegerH = pure ()
checkInfo Int64Info _ = throwError IncorrectInfo
checkInfo BoolInfo BooleanH = pure ()
checkInfo BoolInfo _ = throwError IncorrectInfo
checkInfo UnitInfo UnitH = pure ()
checkInfo UnitInfo _ = throwError IncorrectInfo
checkInfo SumInfo SumH = pure ()
checkInfo SumInfo _ = throwError IncorrectInfo
checkInfo ProductInfo (ProductH _ _) = pure ()
checkInfo ProductInfo _ = throwError IncorrectInfo
checkInfo ListInfo (ListH _) = pure ()
checkInfo ListInfo _ = throwError IncorrectInfo
checkInfo ClosureInfo (ClosureH _) = pure ()
checkInfo ClosureInfo _ = throwError IncorrectInfo
