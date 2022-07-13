
module Hoist.TypeCheck (checkProgram, runTC) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Foldable (traverse_)

import Control.Monad.Reader
import Control.Monad.Except

import Hoist

import qualified CC as C


newtype TC a = TC { getTC :: ReaderT Context (Except TCError) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader Context TC
deriving newtype instance MonadError TCError TC

-- Hmm. 'Name' is used for occurrences, not bindings
-- ...
-- Or something.
--
-- Hmm. ctxNames should be split into 'env' and 'locals'
--
-- Hmm. There should be a separate scope for closure names/types.
data Context = Context { ctxNames :: Map Name Sort, ctxTyVars :: Set C.TyVar }

newtype Signature = Signature (Map DeclName Sort)

lookupName :: Name -> TC Sort
lookupName x = do
  ctx <- asks ctxNames
  case Map.lookup x ctx of
    Just s -> pure s
    Nothing -> throwError $ NameNotInScope x

lookupTyVar :: C.TyVar -> TC ()
lookupTyVar aa = do
  ctx <- asks ctxTyVars
  case Set.member aa ctx of
    True -> pure ()
    False -> throwError $ TyVarNotInScope aa

equalSorts :: Sort -> Sort -> TC ()
equalSorts expected actual =
  when (expected /= actual) $
    throwError (TypeMismatch expected actual)

withPlace :: PlaceName -> TC a -> TC a
withPlace (PlaceName s x) m = do
  checkSort s
  throwError (NotImplemented "withPlace")
  local extend m
  where
    -- Add new local name to context
    extend (Context names tys) = Context names tys

data TCError
  = TypeMismatch Sort Sort
  | NameNotInScope Name
  | TyVarNotInScope C.TyVar
  | NotImplemented String

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT ctx . getTC
  where ctx = Context { ctxNames = Map.empty, ctxTyVars = Set.empty }


checkProgram :: [ClosureDecl] -> TermH -> TC ()
checkProgram [] e = checkEntryPoint e
checkProgram cs e = 
  -- State monad to build signatures
  -- mapAccumL, probably.
  throwError (NotImplemented "checkProgram")

checkEntryPoint :: TermH -> TC ()
checkEntryPoint e = checkClosureBody e

-- checkClosure uses signature and params to populate local context
-- Note: Check that parameters are well-formed
-- (I think I need mapAccumL for this too, because tyvar bindings are in scope
-- for subsequent 'Alloc' or 'Info')
-- (... Hmm. Parameter lists should include tyvars, then.)
-- (Hmm. Remember that 'Info aa' basically acts as a binder for 'aa')
-- (Nonetheless, it would still be cleaner to have (erased) quantifiers, just
-- as singletons still have implicit foralls)
checkClosure :: Signature -> ClosureDecl -> TC ()
checkClosure sig (ClosureDecl cl (envp, envd) params body) = throwError (NotImplemented "checkClosure")

-- | Closure parameters form a telescope, because info bindings bring type
-- variables into scope for subsequent bindings.
checkParams :: [ClosureParam] -> TC Context
checkParams params = throwError (NotImplemented "checkParams")

withParams :: [ClosureParam] -> TC a -> TC a
withParams [] m = m
withParams (PlaceParam p : params) m = withPlace p (withParams params m)
-- withParams (TypeParam i : params) m = local extend (withParams params m)
--   where extend (Context names tys) = Context names (Set.insert i tys)

checkClosureBody :: TermH -> TC ()
checkClosureBody (HaltH x s) = checkSort s *> checkName x s
-- TODO: Sort is not expressive enough to describe polymorphic closures
-- 'ThunkType' will need to be upgraded to work on ClosureParam, not Sort
-- newtype ThunkType = ThunkType [ThunkParam]
-- data ThunkParam = ThunkInfo | ThunkValue Sort ?
checkClosureBody (InstH f ty ss ks) = throwError (NotImplemented "checkClosureBody InstH")
checkClosureBody (LetPrimH p prim e) = do
  s <- checkPrimOp prim
  equalSorts s (placeSort p)
  withPlace p $ checkClosureBody e
checkClosureBody (LetValH p v e) = do
  checkSort (placeSort p)
  checkValue v (placeSort p)
  withPlace p $ checkClosureBody e

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

checkValue :: ValueH -> Sort -> TC ()
checkValue (IntH _) IntegerH = pure ()
checkValue (BoolH _) BooleanH = pure ()
checkValue ListNilH (ListH _) = pure ()


checkName :: Name -> Sort -> TC ()
checkName x s = do
  s' <- lookupName x
  equalSorts s s'

checkSort :: Sort -> TC ()
checkSort (AllocH aa) = lookupTyVar aa
checkSort (InfoH aa) = lookupTyVar aa
checkSort UnitH = pure ()
checkSort IntegerH = pure ()
checkSort BooleanH = pure ()
checkSort SumH = pure ()
checkSort (ProductH t s) = checkSort t *> checkSort s
checkSort (ListH t) = checkSort t
checkSort (ClosureH ss) = traverse_ checkSort ss

checkThunkType :: ThunkType -> TC ()
checkThunkType (ThunkType ss) = throwError (NotImplemented "checkThunkType")
