
-- | A module for lexer utilities and location information.
module Loc
    ( Loc(..)
    , span
    , span'
    , Located(..)

    , noLoc

    , DList
    , dlempty
    , dlsingle
    , snoc
    , rundl
    ) where

-- TODO: This module is very similar to Data.Loc, from package srcloc on Hackage. Consider using that.

import Prelude hiding (span)

-- | Source locations.
data Loc
  = Loc {
    locOffset :: !Int
  , locLine :: !Int
  , locCol :: !Int
  , locLength :: !Int
  }
  deriving (Eq)

instance Ord Loc where
  compare Loc { locOffset = l1 } Loc { locOffset = l2 } = compare l1 l2

instance Show Loc where
  show (Loc _ line col _) = show line ++ ":" ++ show col


-- | Location information missing or unknowable.
noLoc :: Loc
noLoc = Loc { locOffset = -1, locLine = -1, locCol = -1, locLength = 0 }

-- | Create a source location that contains two other source locations.
span :: Loc -> Loc -> Loc
span l1 l2 =
  Loc {
    locOffset = locOffset l1
  , locLine = locLine l1
  , locCol = locCol l1
  , locLength = locOffset l2 + locLength l2 - locOffset l1
  }

-- | A more polymorphic version of 'span', that works on any 'Located' types.
span' :: (Located a, Located b) => a -> b -> Loc
span' x y = span (loc x) (loc y)


-- | A type class for things that have a location.
class Located l where
  -- | Extract the location.
  loc :: l -> Loc



-- | Difference lists.
newtype DList a = DList ([a] -> [a])

-- | The empty difference list.
dlempty :: DList a
dlempty = DList id

-- | A difference list containing a single element.
dlsingle :: a -> DList a
dlsingle x = DList (x:)

-- | Append a single item to a difference list.
snoc :: a -> DList a -> DList a
snoc x (DList xs) = DList $ xs . (x:)

-- | Convert a difference list to a normal list.
rundl :: DList a -> [a]
rundl (DList xs) = xs []

