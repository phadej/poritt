module PoriTT.Meta (
    -- * Meta variables
    MetaVar,
    prettyMetaVar,
    -- * Meta map
    MetaMap,
) where

import PoriTT.PP

import qualified Data.IntMap as IM

-------------------------------------------------------------------------------
-- MetaVar
-------------------------------------------------------------------------------

-- | Meta-variables
newtype MetaVar = MetaVar Int
  deriving (Eq, Ord)

instance Show MetaVar where
    showsPrec d (MetaVar i) = showsPrec d i

instance Enum MetaVar where
    succ (MetaVar i) = MetaVar (i + 1)
    pred (MetaVar i) = MetaVar (i - 1)

    fromEnum (MetaVar i) = i
    toEnum = MetaVar

prettyMetaVar :: MetaVar -> Doc
prettyMetaVar (MetaVar i) = ppAnnotate AErr (ppStr ('?' : show i))

-------------------------------------------------------------------------------
-- MetaMap
-------------------------------------------------------------------------------

-- | Meta map: map indexed by metavariables
newtype MetaMap a = MetaMap (IM.IntMap a)
  deriving (Eq, Ord)

instance Show a => Show (MetaMap a) where
    showsPrec d (MetaMap m) = showsPrec d (IM.toList m)
