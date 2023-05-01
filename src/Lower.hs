
module Lower
    (
    ) where

import qualified Hoist.IR as H

import Control.Monad.Reader
import Data.Int (Int64)

import qualified Data.Map as Map
import Data.Map (Map)



data Program = Program

data Term
  = Open ThunkType NameRef [ClosureArg]
  | Halt NameRef
  | Case NameRef [(Ctor, NameRef)]

  | LetValue (Name, Type) Value Term
  | LetPrim (Name, Type) PrimOp Term
  | LetBindIO (Name, Type) (Name, Type) IOPrimOp Term
  | LetProject (Name, Type) NameRef Projection Term

  | LetClosures [ClosureAlloc] Term

data Value
  = Int64Val Int64
  | StringVal String
  | PairVal NameRef NameRef
  | UnitVal
  | TokenVal
  | Construct CtorApp

data CtorApp
  = BoolCtor Bool
  | InlCtor NameRef
  | InrCtor NameRef
  | CtorApp Ctor [NameRef]

data Projection = ProjectFst | ProjectSnd
data ClosureArg = ValueArg NameRef | TypeArg Type

data ClosureAlloc = ClosureAlloc (Name, Type) ()

data PrimOp = PrimAddInt64 NameRef NameRef

data IOPrimOp = PrimGetLine NameRef


data Type
  = TyInt64


data NameRef = LocalName Name | EnvName Name
  deriving (Eq, Ord)

data Name = Name String
  deriving (Eq, Ord)

data Ctor = Ctor String


data ThunkType = ThunkType { thunkArgs :: [ThunkArg] }
data ThunkArg
  = ThunkValueArg Type
  | ThunkTypeArg -- Kind?


newtype M a = M { getM :: Reader LowerEnv a }

deriving newtype instance Functor M
deriving newtype instance Applicative M
deriving newtype instance Monad M
deriving newtype instance MonadReader LowerEnv M

data LowerEnv = LowerEnv { envThunkTypes :: Map H.Name ThunkType }


lookupThunkType :: H.Name -> M ThunkType
lookupThunkType x = do
  env <- asks envThunkTypes
  case Map.lookup x env of
    Nothing -> error "Name without a thunk type"
    Just ty -> pure ty


lowerProgram :: H.Program -> M Program
lowerProgram (H.Program ds e) = pure Program

lowerTerm :: H.TermH -> M Term
lowerTerm _ = error "Not implemented: lowerTerm"
-- lowerTerm (H.OpenH cl args) =
--   Open <$> lookupThunkType cl <*> lowerName cl <*> traverse lowerClosureArg args

-- lowerName :: H.Name -> M NameRef
-- lowerName x = _

-- lowerClosureArg :: H.ClosureArg -> M ClosureArg
-- lowerClosureArg arg = _
