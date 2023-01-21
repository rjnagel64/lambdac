
module CC.TypeCheck (checkProgram, TypeError(..)) where

import Control.Monad.Except

import CC.IR

data TypeError
  = NotImplemented String

instance Show TypeError where
  show (NotImplemented msg) = "not implemented: " ++ msg


newtype TC a = TC { getTC :: Except TypeError a }

deriving newtype instance Functor TC
deriving newtype instance Applicative TC
deriving newtype instance Monad TC
deriving newtype instance MonadError TypeError TC

runTC :: TC a -> Either TypeError a
runTC = runExcept . getTC

checkProgram :: Program -> Either TypeError ()
checkProgram (Program ds e) = runTC $ do
  throwError (NotImplemented "checkProgram")
