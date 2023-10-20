
module Util where

import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State

commaSep :: [String] -> String
commaSep = intercalate ", "

insertMany :: (Foldable f, Ord k) => f (k, v) -> Map k v -> Map k v
insertMany xs m = foldr (uncurry Map.insert) m xs

mapAccumLM :: (Monad m, Traversable t) => (a -> s -> m (b, s)) -> t a -> s -> m (t b, s)
mapAccumLM f xs s = flip runStateT s $ traverse (StateT . f) xs



newtype One a = One a

instance Functor One where
  fmap f (One x) = One (f x)

instance Foldable One where
  foldMap f (One x) = f x

instance Traversable One where
  traverse f (One x) = One <$> f x


data Two a = Two a a

instance Functor Two where
  fmap f (Two x y) = Two (f x) (f y)

instance Foldable Two where
  foldMap f (Two x y) = f x <> f y

instance Traversable Two where
  traverse f (Two x y) = Two <$> f x <*> f y
