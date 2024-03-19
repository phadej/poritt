module PoriTT.Meta.Entry (
    MetaEntry (..),
    metaEntryType,
) where

import PoriTT.Base
import PoriTT.Term
import PoriTT.Value

data MetaEntry
    = Solved (VTerm HasMetas EmptyCtx) (VTerm HasMetas EmptyCtx)
    | Unsolved (VTerm HasMetas EmptyCtx)
  deriving Show

metaEntryType :: MetaEntry -> VTerm HasMetas EmptyCtx
metaEntryType (Solved ty _) = ty
metaEntryType (Unsolved ty) = ty
