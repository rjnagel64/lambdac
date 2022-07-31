
module Hoist.TypeCheck (checkProgram, runTC, TCError(..)) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Foldable (traverse_, for_)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Hoist


-- TODO: Implement substitution for Hoist types


newtype TC a = TC { getTC :: StateT Signature (ReaderT Context (Except TCError)) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadError TCError TC
deriving newtype instance MonadReader Context TC
deriving newtype instance MonadState Signature TC

-- | The signature stores information about top-level declarations. Currently,
-- this only includes code declarations.
-- Hmm. ThunkType is not really the information we need here.
-- The type of a global code pointer looks like @forall a+. code(t; S)@
data Signature = Signature { sigClosures :: Map ClosureName ThunkType }

-- Represents the type signature 'code[aa+](t; S)'
data ClosureDeclType = ClosureDeclType [TyVar] EnvDeclType ParamTele

type EnvDeclType = ([Sort], [Sort]) -- info types, value types. Maybe use sum type instead?

data ParamTele
  = TeleEnd -- .
  | TypeTele TyVar ParamTele -- forall aa, S
  | InfoTele Sort ParamTele -- info t, S
  | ValueTele Sort ParamTele -- t, S

-- | The typing context is split into two scopes: local information and
-- environment information.
data Context = Context { ctxLocals :: Scope, ctxEnv :: Scope }

-- | A scope contains information about each identifier in scope.
-- Values record their sort, @x : t@.
-- Type variables record their presence, @a : type@.
-- Info variables record the sort they describe, @i : info t@.
data Scope = Scope { scopePlaces :: Map Id Sort, scopeTypes :: Set Id, scopeInfos :: Map Id Sort }

data TCError
  = TypeMismatch Sort Sort
  | NameNotInScope Id
  | TyVarNotInScope TyVar
  | InfoNotInScope Id
  | NotImplemented String
  | IncorrectInfo
  | BadValue
  | BadProjection Sort Projection

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT emptyContext . flip evalStateT emptySignature . getTC
  where
    emptyContext = Context { ctxLocals = emptyScope, ctxEnv = emptyScope }


emptyScope :: Scope
emptyScope = Scope Map.empty Set.empty Map.empty

bindPlace :: Place -> Scope -> Scope
bindPlace (Place s x) (Scope places tys infos) = Scope (Map.insert x s places) tys infos

-- TODO: bindInfo is poorly named
bindInfo :: InfoPlace -> Scope -> Scope
bindInfo (InfoPlace aa) (Scope places tys infos) = Scope places (Set.insert aa tys) infos

emptySignature :: Signature
emptySignature = Signature { sigClosures = Map.empty }

declareClosure :: ClosureName -> ThunkType -> Signature -> Signature
declareClosure cl ty (Signature clos) = Signature (Map.insert cl ty clos)


lookupName :: Name -> TC Sort
lookupName (LocalName x) = do
  ctx <- asks (scopePlaces . ctxLocals)
  case Map.lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInScope x
lookupName (EnvName x) = do
  ctx <- asks (scopePlaces . ctxEnv)
  case Map.lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInScope x

lookupTyVar :: TyVar -> TC ()
lookupTyVar (TyVar aa) = do
  let aa' = Id aa
  ctx <- asks (scopeTypes . ctxLocals)
  case Set.member aa' ctx of
    True -> pure ()
    False -> throwError $ TyVarNotInScope (TyVar aa)

equalSorts :: Sort -> Sort -> TC ()
equalSorts expected actual =
  when (expected /= actual) $
    throwError (TypeMismatch expected actual)

withPlace :: Place -> TC a -> TC a
withPlace p m = do
  checkSort (placeSort p)
  local extend m
  where extend (Context locals env) = Context (bindPlace p locals) env

withInfo :: InfoPlace -> TC a -> TC a
withInfo i m = local extend m
  where extend (Context locals env) = Context (bindInfo i locals) env


checkProgram :: [ClosureDecl] -> TermH -> TC ()
checkProgram cs e = traverse_ checkClosure cs *> checkEntryPoint e

checkEntryPoint :: TermH -> TC ()
checkEntryPoint e = checkClosureBody e

-- | Type-check a top-level code declaration and add it to the signature.
checkClosure :: ClosureDecl -> TC ()
checkClosure (ClosureDecl cl (envp, envd) params body) = do
  -- Check the environment and parameters to populate the typing context
  envScope <- checkEnv envd
  localScope <- checkParams params -- Pass ??? information from env to params??
  -- Use the new scopes to type-check the closure body
  local (\ (Context _ _) -> Context localScope envScope) $ checkClosureBody body
  -- Extend signature
  let f p = case p of { PlaceParam p' -> ThunkValueArg (placeSort p'); TypeParam _ -> ThunkInfoArg }
  let ty = ThunkType (map f params)
  let
    g (PlaceParam p) tele = ValueTele (placeSort p) tele
    g (TypeParam (InfoPlace (Id aa))) tele = TypeTele (TyVar aa) tele
  let tele = foldr g TeleEnd params
  let declTy = ClosureDeclType [] ([], []) tele
  modify (declareClosure cl ty)

checkEnv :: EnvDecl -> TC Scope
checkEnv (EnvDecl tys places) = throwError (NotImplemented "checkEnv")

-- | Closure parameters form a telescope, because info bindings bring type
-- variables into scope for subsequent bindings.
checkParams :: [ClosureParam] -> TC Scope
checkParams [] = pure emptyScope
checkParams (PlaceParam p : params) = withPlace p $ fmap (bindPlace p) (checkParams params)
checkParams (TypeParam i : params) = withInfo i $ fmap (bindInfo i) (checkParams params)

checkClosureBody :: TermH -> TC ()
checkClosureBody (LetValH p v e) = do
  checkSort (placeSort p)
  checkValue v (placeSort p)
  withPlace p $ checkClosureBody e
checkClosureBody (LetPrimH p prim e) = do
  s <- checkPrimOp prim
  equalSorts (placeSort p) s
  withPlace p $ checkClosureBody e
checkClosureBody (LetProjectH p x proj e) = do
  s <- lookupName x
  case (s, proj) of
    (ProductH s' _, ProjectFst) -> equalSorts (placeSort p) s'
    (ProductH _ t', ProjectSnd) -> equalSorts (placeSort p) t'
    (_, _) -> throwError (BadProjection s proj)
  withPlace p $ checkClosureBody e
checkClosureBody (HaltH s x i) = do
  checkName x s
  checkInfo i s
checkClosureBody (OpenH f ty args) = throwError (NotImplemented "checkClosureBody OpenH")
checkClosureBody (CaseH x kind ks) = throwError (NotImplemented "checkClosureBody CaseH")
-- Extend env with places for each closure
-- type check each closure/env application
checkClosureBody (AllocClosure cs e) = do
  let binds = map closurePlace cs
  -- withPlaces binds $
  for_ cs $ \ (ClosureAlloc p c env) -> do
    -- Look up type of closure decl ([polymorphic] code type)
    -- Use closure type to check environment allocation
    -- check that place sort matches code type?
    throwError (NotImplemented "checking closure alloc")
  -- withPlaces binds $
  checkClosureBody e

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

checkName :: Name -> Sort -> TC ()
checkName x s = do
  s' <- lookupName x
  equalSorts s s'

-- | Check that a sort is well-formed w.r.t. the context
checkSort :: Sort -> TC ()
checkSort (AllocH aa) = lookupTyVar aa
checkSort UnitH = pure ()
checkSort IntegerH = pure ()
checkSort BooleanH = pure ()
checkSort SumH = pure ()
checkSort (ProductH t s) = checkSort t *> checkSort s
checkSort (ListH t) = checkSort t
checkSort (ClosureH ss) = traverse_ checkSort ss

-- | Given info @i@ and sort @s@, check that @Γ |- i : info s@.
checkInfo :: Info -> Sort -> TC ()
checkInfo (LocalInfo i) s = do
  infos <- asks (scopeInfos . ctxLocals)
  case Map.lookup i infos of
    Nothing -> throwError (InfoNotInScope i)
    Just s' -> equalSorts s s'
checkInfo (EnvInfo i) s = do
  infos <- asks (scopeInfos . ctxEnv)
  case Map.lookup i infos of
    Nothing -> throwError (InfoNotInScope i)
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
