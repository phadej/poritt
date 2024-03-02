module PoriTT.Rigid (
    -- * Meta variables
    RigidVar,
    prettyRigidVar,
    -- * Meta map
    RigidMap,
) where

import PoriTT.Base
import PoriTT.PP

import qualified Data.IntMap as IM

-------------------------------------------------------------------------------
-- Rigid
-------------------------------------------------------------------------------

-- | Meta-variables
type RigidVar :: Ctx -> Type
newtype RigidVar ctx = RigidVar Int
  deriving (Eq, Ord)

instance Show (RigidVar ctx) where
    showsPrec d (RigidVar i) = showsPrec d i

prettyRigidVar :: RigidVar ctx -> Doc
prettyRigidVar (RigidVar i) = ppAnnotate AErr (ppStr ('!' : show i))


instance Renamable RigidVar where
    rename = defaultRename
    weaken _ (RigidVar x) = RigidVar x

instance RenamableA RigidVar where
    grename _ (RigidVar x) = pure (RigidVar x)

-------------------------------------------------------------------------------
-- RigidMap
-------------------------------------------------------------------------------

-- | Meta map: map indexed by Rigids
type RigidMap :: Ctx -> Type -> Type
newtype RigidMap ctx a = RigidMap (IM.IntMap a)
  deriving (Eq, Ord)

instance Show a => Show (RigidMap ctx a) where
    showsPrec d (RigidMap m) = showsPrec d (IM.toList m)
