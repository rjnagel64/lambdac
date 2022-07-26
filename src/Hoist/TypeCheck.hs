
module Hoist.TypeCheck (checkProgram, runTC) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Foldable (traverse_)

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Hoist

import qualified CC as C


newtype TC a = TC { getTC :: StateT Signature (ReaderT Context (Except TCError)) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadState Signature TC
deriving newtype instance MonadReader Context TC
deriving newtype instance MonadError TCError TC

-- Hmm. ThunkType is not really the information we need here.
-- The type of a global code pointer looks like @forall a+. code(t; S)@
data Signature = Signature { sigClosures :: Map ClosureName ThunkType }

data Context = Context { ctxLocals :: Scope, ctxEnv :: Scope }

data Scope = Scope { scopePlaces :: Map Id Sort, scopeTypes :: Set Id }

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

lookupTyVar :: C.TyVar -> TC ()
lookupTyVar (C.TyVar aa) = do
  -- TODO: C.TyVar doesn't really make sense here.
  let aa' = Id aa
  ctx <- asks (scopeTypes . ctxLocals)
  case Set.member aa' ctx of
    True -> pure ()
    False -> throwError $ TyVarNotInScope (C.TyVar aa)

equalSorts :: Sort -> Sort -> TC ()
equalSorts expected actual =
  when (expected /= actual) $
    throwError (TypeMismatch expected actual)

withPlace :: Place -> TC a -> TC a
withPlace (Place s x) m = do
  checkSort s
  local extend m
  where
    extend (Context (Scope places tys) env) = Context (Scope (Map.insert x s places) tys) env

withInfo :: InfoPlace -> TC a -> TC a
withInfo (InfoPlace aa) m = local extend m
  where
    extend (Context (Scope places tys) env) = Context (Scope places (Set.insert aa tys)) env

data TCError
  = TypeMismatch Sort Sort
  | NameNotInScope Id
  | TyVarNotInScope C.TyVar
  | NotImplemented String
  | IncorrectInfo
  | BadValue
  | BadProjection Sort Projection

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT emptyContext . flip evalStateT emptySig . getTC
  where
    emptyContext = Context { ctxLocals = emptyScope, ctxEnv = emptyScope }
    emptyScope = Scope Map.empty Set.empty
    emptySig = Signature { sigClosures = Map.empty }


checkProgram :: [ClosureDecl] -> TermH -> TC ()
checkProgram [] e = checkEntryPoint e
checkProgram cs e = 
  -- State monad to build signatures
  -- mapAccumL, probably.
  throwError (NotImplemented "checkProgram")

checkEntryPoint :: TermH -> TC ()
checkEntryPoint e = checkClosureBody e

checkClosure :: ClosureDecl -> TC ()
checkClosure (ClosureDecl cl (envp, envd) params body) = do
  -- _ <- checkEnv envd
  _ <- checkParams params
  -- withEnv env
  withParams params $ checkClosureBody body
  -- Extend signature
  -- modify _

checkEnv :: EnvDecl -> TC Scope
checkEnv (EnvDecl tys places) = throwError (NotImplemented "checkEnv")

-- | Closure parameters form a telescope, because info bindings bring type
-- variables into scope for subsequent bindings.
checkParams :: [ClosureParam] -> TC Context
checkParams params = throwError (NotImplemented "checkParams")

withParams :: [ClosureParam] -> TC a -> TC a
withParams [] m = m
withParams (PlaceParam p : params) m = withPlace p (withParams params m)
withParams (TypeParam i : params) m = withInfo i (withParams params m)

checkClosureBody :: TermH -> TC ()
checkClosureBody (HaltH x i) = do
  s <- lookupName x
  checkInfo s i
checkClosureBody (OpenH f ty args) = throwError (NotImplemented "checkClosureBody OpenH")
checkClosureBody (LetPrimH p prim e) = do
  s <- checkPrimOp prim
  equalSorts (placeSort p) s
  withPlace p $ checkClosureBody e
checkClosureBody (LetValH p v e) = do
  checkSort (placeSort p)
  checkValue v (placeSort p)
  withPlace p $ checkClosureBody e
checkClosureBody (LetProjectH p x proj e) = do
  s <- lookupName x
  case (s, proj) of
    (ProductH s' _, ProjectFst) -> equalSorts (placeSort p) s'
    (ProductH _ t', ProjectSnd) -> equalSorts (placeSort p) t'
    (_, _) -> throwError (BadProjection s proj)
  withPlace p $ checkClosureBody e

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
  checkInfo s i
checkValue (InlH _ _) _ = throwError BadValue
checkValue (InrH i x) SumH = do
  s <- lookupName x
  checkInfo s i
checkValue (InrH _ _) _ = throwError BadValue
checkValue (PairH i j x y) (ProductH s t) = do
  s' <- lookupName x
  t' <- lookupName y
  equalSorts s s'
  equalSorts t t'
  checkInfo s' i
  checkInfo t' j
checkValue (PairH _ _ _ _) _ = throwError BadValue
checkValue ListNilH (ListH _) = pure ()
checkValue ListNilH _ = throwError BadValue
checkValue (ListConsH i x xs) (ListH t) = do
  checkInfo t i
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

-- | Check that info @i@ describes sort @s@.
checkInfo :: Sort -> Info -> TC ()
checkInfo (AllocH aa) (LocalInfo bb) = do
  -- TODO: checkInfo AllocH: aa should equal bb, right?
  ctx <- asks (scopeTypes . ctxEnv)
  case Set.member bb ctx of
    False -> throwError (NameNotInScope bb)
    True -> pure ()
checkInfo (AllocH aa) (EnvInfo bb) = do
  ctx <- asks (scopeTypes . ctxEnv)
  case Set.member bb ctx of
    False -> throwError (NameNotInScope bb)
    True -> pure ()
-- Polymorphic sort should not have monomorphic info
checkInfo (AllocH _) _ = throwError IncorrectInfo
checkInfo IntegerH Int64Info = pure ()
checkInfo IntegerH _ = throwError IncorrectInfo
checkInfo BooleanH BoolInfo = pure ()
checkInfo BooleanH _ = throwError IncorrectInfo
checkInfo UnitH UnitInfo = pure ()
checkInfo UnitH _ = throwError IncorrectInfo
checkInfo SumH SumInfo = pure ()
checkInfo SumH _ = throwError IncorrectInfo
