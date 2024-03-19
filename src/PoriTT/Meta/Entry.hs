module PoriTT.Meta.Entry (
    MetaEntry (..),
    metaEntryType,
) where

import PoriTT.Base
import PoriTT.Term
import PoriTT.Value

data MetaEntry
    = Solved (Term HasMetas EmptyCtx) (VTerm HasMetas EmptyCtx) (Term HasMetas EmptyCtx) (VTerm HasMetas EmptyCtx)
    | Unsolved (Term HasMetas EmptyCtx) (VTerm HasMetas EmptyCtx)
  deriving Show

metaEntryType :: MetaEntry -> VTerm HasMetas EmptyCtx
metaEntryType (Solved _ ty _ _) = ty
metaEntryType (Unsolved _ ty)   = ty
