module PoriTT.Meta (
    -- * Meta variables
    MetaVar,
    prettyMetaVar,
    -- * Meta map
    MetaMap,
    emptyMetaMap,
    lookupMetaMap,
    insertMetaMap,
    -- * Meta state
    MetaGen,
    initialMetaGen,
    newMetaVar,
) where

import PoriTT.PP
import PoriTT.Base

import Optics.Core (castOptic, simple)

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


emptyMetaMap :: MetaMap a
emptyMetaMap = MetaMap IM.empty

insertMetaMap :: MetaVar -> a -> MetaMap a -> MetaMap a
insertMetaMap (MetaVar k) v (MetaMap m) = MetaMap (IM.insert k v m)

lookupMetaMap :: MetaVar -> MetaMap a -> Maybe a
lookupMetaMap (MetaVar k) (MetaMap m) = IM.lookup k m

-------------------------------------------------------------------------------
-- MetaGen
-------------------------------------------------------------------------------

newtype MetaGen = MetaGen Int
  deriving Show

initialMetaGen :: MetaGen
initialMetaGen = MetaGen 0

class HasMetaGen s where
    metaGen :: Lens' s MetaGen

instance HasMetaGen MetaGen where
    metaGen = castOptic simple

newMetaVar :: (MonadState s m, HasMetaGen s) => m MetaVar
newMetaVar = do
    s <- get
    let MetaGen r = view metaGen s
    put $! set metaGen (MetaGen (r + 1)) s
    return (MetaVar r)
