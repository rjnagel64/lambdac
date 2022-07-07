
module Hoist.TypeCheck (checkProgram) where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Foldable (traverse_)

import Control.Monad.Reader
import Control.Monad.Except

import Hoist

import qualified CC as C
import CC (Sort(..))


newtype TC a = TC { getTC :: ReaderT Context (Except TCError) a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadReader Context TC
deriving newtype instance MonadError TCError TC

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

data TCError
  = TypeMismatch Sort Sort
  | NameNotInScope Name
  | TyVarNotInScope C.TyVar
  | NotImplemented String

runTC :: TC a -> Either TCError a
runTC = runExcept . flip runReaderT ctx . getTC
  where ctx = Context { ctxNames = Map.empty, ctxTyVars = Set.empty }


checkProgram :: [ClosureDecl] -> TermH -> Either TCError ()
checkProgram cs e = 
  -- State monad to build signatures
  -- mapAccumL, probably.
  throwError (NotImplemented "checkProgram")

-- checkClosure uses signature and params to populate local context
-- Note: Check that parameters are well-formed
-- (I think I need mapAccumL for this too, because tyvar bindings are in scope
-- for subsequent 'Alloc' or 'Info')
-- (... Hmm. Parameter lists should include tyvars, then.)
checkClosure :: Signature -> ClosureDecl -> Except TCError ()
checkClosure sig (ClosureDecl cl (envp, envd) params body) = throwError (NotImplemented "checkClosure")

checkClosureBody :: TermH -> TC ()
checkClosureBody (HaltH x s) = checkName x s


checkName :: Name -> Sort -> TC ()
checkName x s = do
  checkSort s
  s' <- lookupName x
  when (s' /= s) $
    throwError $ TypeMismatch s s'

checkSort :: Sort -> TC ()
checkSort (Alloc aa) = lookupTyVar aa
checkSort (Info aa) = lookupTyVar aa
checkSort Unit = pure ()
checkSort Integer = pure ()
checkSort Boolean = pure ()
checkSort Sum = pure ()
checkSort (Pair t s) = checkSort t *> checkSort s
checkSort (List t) = checkSort t
checkSort (Closure ss) = traverse_ checkSort ss
