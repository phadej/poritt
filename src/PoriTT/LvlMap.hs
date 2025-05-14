-- | Partial renaming
module PoriTT.LvlMap (
    LvlMap,
    lookupLvlMap,
    emptyLvlMap,
    insertLvlMap,
    deleteLvlMap,
    sinkLvlMap,
) where

import PoriTT.Base

import DeBruijn.Internal.Lvl

import qualified Data.IntMap as IM

type LvlMap :: Ctx -> Type -> Type
newtype LvlMap ctx a = UnsafeLvlMap (IM.IntMap a)
  deriving (Functor, Show)

lookupLvlMap :: Lvl ctx -> LvlMap ctx a -> Maybe a
lookupLvlMap (UnsafeLvl i) (UnsafeLvlMap m) = IM.lookup i m

emptyLvlMap :: Size ctx -> LvlMap ctx a
emptyLvlMap _s = UnsafeLvlMap IM.empty

insertLvlMap :: Lvl ctx -> a -> LvlMap ctx a -> LvlMap ctx a
insertLvlMap (UnsafeLvl k) v (UnsafeLvlMap m) = UnsafeLvlMap (IM.insert k v m)

deleteLvlMap :: Lvl ctx -> LvlMap ctx a -> LvlMap ctx a
deleteLvlMap  (UnsafeLvl k) (UnsafeLvlMap m) = UnsafeLvlMap (IM.delete k m)

sinkLvlMap :: LvlMap ctx a -> LvlMap (S ctx) a
sinkLvlMap = coerce
