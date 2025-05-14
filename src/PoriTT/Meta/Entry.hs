module PoriTT.Meta.Entry (
    MetaEntry (..),
    metaEntryType,
    forceElim,
    forceTerm,
) where

import PoriTT.Base
import PoriTT.Term
import PoriTT.Eval
import PoriTT.Value
import PoriTT.Meta.Var

data MetaEntry
    = Solved (VTerm HasMetas EmptyCtx) (VTerm HasMetas EmptyCtx)
    | Unsolved (VTerm HasMetas EmptyCtx)
  deriving Show

metaEntryType :: MetaEntry -> VTerm HasMetas EmptyCtx
metaEntryType (Solved ty _) = ty
metaEntryType (Unsolved ty) = ty

forceElim :: Size ctx -> MetaMap MetaEntry -> VElim pass ctx -> VElim pass ctx
forceElim s xs e = case e of
    VFlx m sp | Just (Solved ty v) <- lookupMetaMap m xs ->
        forceElim s xs (vappSpine s (sinkSize s (vann v ty)) sp)
    _                       -> e

forceTerm :: Size ctx -> MetaMap MetaEntry -> VTerm pass ctx -> VTerm pass ctx
forceTerm s xs (VEmb e) = vemb (forceElim s xs e)
forceTerm _ _  t        = t
