module PoriTT.Rigid (
    -- * Rigid variables
    RigidVar,
    prettyRigidVar,
    -- * Rigid map
    RigidMap,
    -- * Rigid State
    RigidState,
    initialRigidState,
    HasRigidState (..),
    takeRigidVar,
) where

import PoriTT.Base
import PoriTT.PP

import Optics.Core (castOptic, simple)

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

instance Sinkable RigidVar where
    mapLvl _ (RigidVar x) = RigidVar x

-------------------------------------------------------------------------------
-- RigidMap
-------------------------------------------------------------------------------

-- | Meta map: map indexed by Rigids
type RigidMap :: Ctx -> Type -> Type
newtype RigidMap ctx a = RigidMap (IM.IntMap a)
  deriving (Eq, Ord)

instance Show a => Show (RigidMap ctx a) where
    showsPrec d (RigidMap m) = showsPrec d (IM.toList m)

-------------------------------------------------------------------------------
-- RigidState
-------------------------------------------------------------------------------

newtype RigidState = RigidState Int
  deriving Show

initialRigidState :: RigidState
initialRigidState = RigidState 0

class HasRigidState s where
    rigidState :: Lens' s RigidState

instance HasRigidState RigidState where
    rigidState = castOptic simple

takeRigidVar :: (MonadState s m, HasRigidState s) => m (RigidVar ctx)
takeRigidVar = do
    s <- get
    let RigidState r = view rigidState s
    put $! set rigidState (RigidState (r + 1)) s
    return (RigidVar r)
