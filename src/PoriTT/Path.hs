module PoriTT.Path (
    Path (..),
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.Term
import PoriTT.Value

-- | A "context zipper", used for efficiently creating types for fresh metas.
type Path :: Ctx -> Ctx -> Type
data Path ctx ctx' where
    PEnd    :: Path ctx ctx
    PDefine :: !(Path ctx ctx') -> !Name -> (VTerm HasMetas ctx') -> EvalElim HasMetas ctx' -> Path ctx ctx'
    PBind   :: !(Path ctx ctx') -> !Name -> (VTerm HasMetas ctx') -> Path ctx (S ctx')
