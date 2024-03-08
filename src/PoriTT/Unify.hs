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
