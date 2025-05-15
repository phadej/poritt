{-# LANGUAGE CPP #-}
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

#ifdef MIN_VERSION_debruijn

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

#else

import qualified Data.Map as M

type LvlMap :: Ctx -> Type -> Type
newtype LvlMap ctx a = LvlMap (M.Map (Lvl ctx) a)
  deriving (Functor, Show)

lookupLvlMap :: Lvl ctx -> LvlMap ctx a -> Maybe a
lookupLvlMap i (LvlMap m) = M.lookup i m

emptyLvlMap :: Size ctx -> LvlMap ctx a
emptyLvlMap _s = LvlMap M.empty

insertLvlMap :: Lvl ctx -> a -> LvlMap ctx a -> LvlMap ctx a
insertLvlMap k v (LvlMap m) = LvlMap (M.insert k v m)

deleteLvlMap :: Lvl ctx -> LvlMap ctx a -> LvlMap ctx a
deleteLvlMap  k (LvlMap m) = LvlMap (M.delete k m)

sinkLvlMap :: LvlMap ctx a -> LvlMap (S ctx) a
sinkLvlMap (LvlMap m) = LvlMap (M.mapKeys sink m)

#endif
