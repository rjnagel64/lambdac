
module Hoist.TypeCheck (checkProgram, runTC, TCError(..)) where

import qualified Data.Map as Map
import Data.Map (Map)

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

-- | The signature stores information about top-level declarations.
data Signature
  = Signature {
    sigClosures :: Map CodeLabel ClosureDeclType
  , sigTyCons :: Map TyCon Kind
  }

-- | Represents the type of a closure, a code pointer with environment
-- @code(t; S)@.
data ClosureDeclType = ClosureDeclType EnvType ClosureTele

-- | Represents the type of a closure environment, @∃(aa : k)+. { (l : s)+ }@.
data EnvType = EnvType { envTyVars :: [(TyVar, Kind)], envFields :: [(Id, Sort)] }

-- | The typing context contains the type of each item in scope, plus the type
-- of the environment parameter.
-- (The environment is still somewhat special, so it cannot simply be included in Locals)
data Context = Context { ctxLocals :: Locals, ctxEnv :: EnvType }

-- | The local scope contains information about each identifier in the context,
-- except for the closure environment.
-- Values record their sort, @x : t@.
-- Type variables record their kind, @aa : k@.
data Locals = Locals { localPlaces :: Map Id Sort, localTypes :: Map TyVar Kind }

-- | Ways in which a Hoist IR program can be invalid.
data TCError
  = TypeMismatch Sort Sort
  | KindMismatch Kind Kind
  | NameNotInLocals Id
  | TyVarNotInLocals TyVar
  | TyConNotInScope TyCon
  | ClosureNotInLocals CodeLabel
  | InfoNotInLocals Id
  | NotImplemented String
  | IncorrectInfo
  | BadValue
  | BadProjection Sort Projection
  | BadCase TyConApp [(Ctor, Name)]
  | BadOpen Name Sort
  | WrongClosureArg
  | ArgumentCountMismatch
  | DuplicateLabels [String]
  | BadCtorApp
  | BadTyApp

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT emptyContext . flip evalStateT emptySignature . getTC
  where
    emptyContext = Context { ctxLocals = emptyLocals, ctxEnv = emptyEnv }
    -- Dummy value, as the program entry point is not in a closure decl, so it
    -- does not have an environment parameter.
    --
    -- Therefore, use @∃.{}@, which is isomorphic to ().
    emptyEnv = EnvType { envTyVars = [], envFields = [] }


emptyLocals :: Locals
emptyLocals = Locals Map.empty Map.empty

emptySignature :: Signature
emptySignature = Signature { sigClosures = Map.empty, sigTyCons = Map.empty }

declareClosure :: CodeLabel -> ClosureDeclType -> Signature -> Signature
declareClosure cl ty (Signature clos tcs) = Signature (Map.insert cl ty clos) tcs


lookupName :: Name -> TC Sort
lookupName (LocalName x) = do
  ctx <- asks (localPlaces . ctxLocals)
  case Map.lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInLocals x
lookupName (EnvName x) = do
  ctx <- asks (envFields . ctxEnv)
  case lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInLocals x

lookupTyVar :: TyVar -> TC Kind
lookupTyVar aa = do
  ctx <- asks (localTypes . ctxLocals)
  case Map.lookup aa ctx of
    Just k -> pure k
    Nothing -> throwError $ TyVarNotInLocals aa

lookupTyCon :: TyCon -> TC Kind
lookupTyCon tc = do
  ctx <- gets sigTyCons
  case Map.lookup tc ctx of
    Just k -> pure k
    Nothing -> throwError $ TyConNotInScope tc

lookupCodeDecl :: CodeLabel -> TC ClosureDeclType
lookupCodeDecl c = do
  sig <- gets sigClosures
  case Map.lookup c sig of
    Just t -> pure t
    Nothing -> throwError $ ClosureNotInLocals c

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
  where extend (Context (Locals places tys) env) = Context (Locals (Map.insert x s places) tys) env

withPlaces :: [Place] -> TC a -> TC a
withPlaces ps = foldr (.) id (map withPlace ps)

withTyVar :: TyVar -> Kind -> TC a -> TC a
withTyVar aa k m = local (\ (Context locals env) -> Context (extend locals) env) m
  where
    extend (Locals places tys) = Locals places (Map.insert aa k tys)




checkName :: Name -> Sort -> TC ()
checkName x s = do
  s' <- lookupName x
  equalSorts s s'


checkProgram :: Program -> TC ()
checkProgram (Program ds e) = traverse_ checkDecl ds *> checkEntryPoint e

checkDecl :: Decl -> TC ()
checkDecl (DeclCode cd) = checkCodeDecl cd
checkDecl (DeclData dd) = throwError (NotImplemented "check DataDecl")

checkEntryPoint :: TermH -> TC ()
checkEntryPoint e = checkTerm e

-- | Type-check a top-level code declaration and add it to the signature.
checkCodeDecl :: CodeDecl -> TC ()
checkCodeDecl decl@(CodeDecl cl (envp, envd) params body) = do
  -- Check the environment and parameters to populate the environment scope for
  -- the typing context
  envTy <- checkEnvDecl envd
  -- Check that the parameter list is well-formed, and extract the initial
  -- contents of the local scope for the typing context.
  localScope <- local (\ (Context _ _) -> Context emptyLocals envTy) $ checkParams params
  -- Use the parameter list and environment to type-check the closure body.
  local (\ (Context _ _) -> Context localScope envTy) $ checkTerm body
  -- Extend the signature with the new closure declaration.
  let tele = codeDeclTele decl
  let declTy = ClosureDeclType envTy tele
  modify (declareClosure cl declTy)

checkEnvDecl :: EnvDecl -> TC EnvType
-- Check that all (info/field) labels are disjoint, and that each field type is
-- well-formed.
checkEnvDecl (EnvDecl tys places) = do
  checkUniqueLabels [placeName p | p <- places]

  -- Hmm. I think I need to bring 'tys' into scope to check the sorts here,
  -- since 'tys' are like a sequence of existential quantifiers.
  fields <- for places $ \ (Place s x) -> do
    checkSort s Star
    pure (x, s)
  pure (EnvType tys fields)

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
checkParams [] = asks ctxLocals
checkParams (PlaceParam p : params) = withPlace p $ checkParams params
checkParams (TypeParam aa k : params) = withTyVar aa k $ checkParams params

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
      ClosureDeclType envTy tele <- lookupCodeDecl c
      checkEnvAlloc env envTy
      equalSorts (placeSort p) (ClosureH tele)
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
checkCallArgs (ValueTele _ : _) (_ : _) = throwError WrongClosureArg
checkCallArgs (TypeTele aa k : tele) (TypeArg s : args) = do
  checkSort s k
  let tele' = substTele (singleSubst aa s) tele
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
-- checkValue (BoolH _) BooleanH = pure ()
-- checkValue (BoolH _) _ = throwError BadValue
checkValue NilH UnitH = pure ()
checkValue NilH _ = throwError BadValue
-- checkValue (InlH x) (SumH t s) = do
--   checkName x t
-- checkValue (InlH _) _ = throwError BadValue
-- checkValue (InrH y) (SumH t s) = do
--   checkName y s
-- checkValue (InrH _) _ = throwError BadValue
checkValue (PairH x y) (ProductH s t) = do
  checkName x s
  checkName y t
checkValue (PairH _ _) _ = throwError BadValue
-- checkValue ListNilH (ListH _) = pure ()
-- checkValue ListNilH _ = throwError BadValue
-- checkValue (ListConsH x xs) (ListH t) = do
--   checkName x t
--   checkName xs (ListH t) 
-- checkValue (ListConsH _ _) _ = throwError BadValue
checkValue (StringValH _) StringH = pure ()
checkValue (StringValH _) _ = throwError BadValue
checkValue (CtorAppH capp) s = case asTyConApp s of
  Nothing -> throwError BadCtorApp
  Just tcapp -> checkCtorApp capp tcapp

checkCtorApp :: CtorAppH -> TyConApp -> TC ()
checkCtorApp (BoolH _) CaseBool = pure ()
checkCtorApp _ CaseBool = throwError BadCtorApp 
checkCtorApp (InlH x) (CaseSum t s) = checkName x t
checkCtorApp (InrH y) (CaseSum t s) = checkName y s
checkCtorApp _ (CaseSum _ _) = throwError BadCtorApp
checkCtorApp ListNilH (CaseList _) = pure ()
checkCtorApp (ListConsH x xs) (CaseList t) = checkName x t *> checkName xs (ListH t)

-- I think I need something like DataDesc here.
-- * Check scrutinee has same type as the TyConApp
-- * Check coverage of branches?
-- * Lookup ctor, use that to check type of continuation
checkCase :: Name -> TyConApp -> [(Ctor, Name)] -> TC ()
checkCase x CaseBool [(cf, kf), (ct, kt)] = do
  checkName x BooleanH
  checkName kf (ClosureH (ClosureTele []))
  checkName kt (ClosureH (ClosureTele []))
checkCase x (CaseSum a b) [(cl, kl), (cr, kr)] = do
  checkName x (SumH a b)
  checkName kl (ClosureH (ClosureTele [ValueTele a]))
  checkName kr (ClosureH (ClosureTele [ValueTele b]))
checkCase x (CaseList a) [(cn, kn), (cc, kc)] = do
  checkName x (ListH a)
  checkName kn (ClosureH (ClosureTele []))
  checkName kc (ClosureH (ClosureTele [ValueTele a, ValueTele (ListH a)]))
checkCase _ kind ks = throwError (BadCase kind ks)

-- | Check that a sort is well-formed w.r.t. the context
inferSort :: Sort -> TC Kind
inferSort (AllocH aa) = lookupTyVar aa
inferSort UnitH = pure Star
inferSort IntegerH = pure Star
inferSort BooleanH = pure Star
inferSort StringH = pure Star
inferSort (ProductH t s) = checkSort t Star *> checkSort s Star *> pure Star
inferSort (SumH t s) = checkSort t Star *> checkSort s Star *> pure Star
inferSort (ListH t) = checkSort t Star *> pure Star
inferSort (ClosureH tele) = checkTele tele *> pure Star
inferSort (TyConH tc) = lookupTyCon tc
inferSort (TyAppH t s) = do
  inferSort t >>= \case
    KArr k1 k2 -> checkSort s k1 *> pure k2
    Star -> throwError BadTyApp

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

