module PoriTT.Enum (
    -- * Enumeration indices
    EnumIdx (..),
    prettyEnumIdx,
    -- * Enumeration list
    EnumList (..),
    makeEnumList,
    lookupEnumList,
) where

import PoriTT.Base
import PoriTT.PP

import Data.Foldable.WithIndex    (FoldableWithIndex (..))
import Data.Functor.WithIndex     (FunctorWithIndex (..))
import Data.Traversable.WithIndex (TraversableWithIndex (..))

import qualified Data.SkewList.Lazy as SL

-------------------------------------------------------------------------------
-- EnumIdx
-------------------------------------------------------------------------------

-- | Enumeration index.
newtype EnumIdx = EnumIdx Int
  deriving (Eq, Ord)

instance Show EnumIdx where
    showsPrec d (EnumIdx i) = showsPrec d i

prettyEnumIdx :: EnumIdx -> Doc
prettyEnumIdx (EnumIdx i) = ppAnnotate ALbl (ppStr (':' : show i))

-------------------------------------------------------------------------------
-- EnumList
-------------------------------------------------------------------------------

newtype EnumList a = EnumList (SkewList a)
  deriving newtype (Eq, Ord, Show)
  deriving stock (Functor, Foldable, Traversable)

instance FunctorWithIndex EnumIdx EnumList where
    imap f (EnumList xs) = EnumList (imap (f . EnumIdx) xs)

instance FoldableWithIndex EnumIdx EnumList where
    ifoldr f z (EnumList xs) = ifoldr (f . EnumIdx) z xs

instance TraversableWithIndex EnumIdx EnumList where
    itraverse f (EnumList xs) = EnumList <$> itraverse (f . EnumIdx) xs

makeEnumList :: [a] -> EnumList a
makeEnumList = EnumList . SL.fromList

lookupEnumList :: EnumIdx -> EnumList a -> Maybe a
lookupEnumList (EnumIdx i) (EnumList xs) = xs SL.!? i
