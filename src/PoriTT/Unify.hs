module PoriTT.Unify (
    UnifyEnv (..),
) where

import PoriTT.Base
import PoriTT.Elab.Monad
import PoriTT.Name
import PoriTT.Term
import PoriTT.Rigid
import PoriTT.Value

data UnifyEnv ctx = UnifyEnv
    { size   :: Size ctx
    , names  :: Env ctx Name
    , types  :: Env ctx (VTerm HasMetas ctx)
    , nscope :: NameScope
    , rigids :: RigidMap ctx (VTerm HasMetas ctx)
    }

bind :: Name -> VTerm HasMetas ctx -> UnifyEnv ctx -> UnifyEnv (S ctx)
bind x t (UnifyEnv s xs ts gs rs) = UnifyEnv (SS s) (xs :> x) (mapSink ts :> sink t) gs (rigidMapSink (mapSink rs))
