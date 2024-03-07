module PoriTT.Rigid (
    -- * Rigid variables
    RigidVar,
    prettyRigidVar,
    -- * Rigid map
    RigidMap,
    emptyRigidMap,
    insertRigidMap,
    lookupRigidMap,
    rigidMapSink,
    -- * Rigid State
    RigidGen,
    initialRigidGen,
    HasRigidGen (..),
    newRigidVar,
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
  deriving (Eq, Ord, Functor)

instance Show a => Show (RigidMap ctx a) where
    showsPrec d (RigidMap m) = showsPrec d (IM.toList m)

emptyRigidMap :: RigidMap ctx a
emptyRigidMap = RigidMap IM.empty

insertRigidMap :: RigidVar ctx -> a -> RigidMap ctx a -> RigidMap ctx a
insertRigidMap (RigidVar k) v (RigidMap m) = RigidMap (IM.insert k v m)

lookupRigidMap :: RigidVar ctx -> RigidMap ctx a -> Maybe a
lookupRigidMap (RigidVar k) (RigidMap m) = IM.lookup k m

rigidMapSink :: RigidMap ctx a -> RigidMap (S ctx) a
rigidMapSink = coerce

-------------------------------------------------------------------------------
-- RigidGen
-------------------------------------------------------------------------------

newtype RigidGen = RigidGen Int
  deriving Show

initialRigidGen :: RigidGen
initialRigidGen = RigidGen 0

class HasRigidGen s where
    rigidGen :: Lens' s RigidGen

instance HasRigidGen RigidGen where
    rigidGen = castOptic simple

newRigidVar :: (MonadState s m, HasRigidGen s) => m (RigidVar ctx)
newRigidVar = do
    s <- get
    let RigidGen r = view rigidGen s
    put $! set rigidGen (RigidGen (r + 1)) s
    return (RigidVar r)
