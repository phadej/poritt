module PoriTT.Elab.Ctx (
    ElabCtx (..),
    bind,
    bind',
    emptyElabCtx,
) where

import PoriTT.Base
import PoriTT.Loc
import PoriTT.Meta
import PoriTT.Name
import PoriTT.PP
import PoriTT.Rigid
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Value

-------------------------------------------------------------------------------
-- Elaboration context
-------------------------------------------------------------------------------

-- | Elaboration context.
--
data ElabCtx ctx ctx' = ElabCtx
    { names  :: !(Env ctx Name)
    , names' :: !(Env ctx' Name)
    , nscope :: !NameScope
    , values :: !(EvalEnv HasMetas ctx ctx')
    , types  :: !(Env ctx (VTerm HasMetas ctx'))
    , types' :: !(Env ctx' (VTerm HasMetas ctx'))
    , rigids :: !(RigidMap ctx' (VTerm HasMetas ctx'))
    , mtypes :: !(MetaMap (VTerm HasMetas EmptyCtx))
    , stages :: !(Env ctx Stage)
    , cstage :: !Stage
    , size   :: !(Size ctx')
    , wk     :: Wk ctx' ctx               -- ^ weakening from target context to source context. This is possible, as target context is the same except the let bound values are missing.
    , loc    :: !(Loc)
    , doc    :: ![Doc]
    }

-- | Empty elaboration context.
--
-- Needs global 'NameScope' for pretty-printing.
--
emptyElabCtx :: NameScope -> ElabCtx EmptyCtx EmptyCtx
emptyElabCtx ns = ElabCtx
    { names  = EmptyEnv
    , names' = EmptyEnv
    , nscope = ns
    , values = EmptyEnv
    , types  = EmptyEnv
    , types' = EmptyEnv
    , rigids = emptyRigidMap
    , mtypes = emptyMetaMap
    , stages = EmptyEnv
    , cstage = stage0
    , size   = SZ
    , wk     = IdWk
    , loc    = startLoc "<unknown>"
    , doc    = []
    }

bind
    :: ElabCtx ctx ctx'
    -> Name                     -- ^ term name
    -> Name                     -- ^ name in types
    -> VTerm HasMetas ctx'      -- ^ type
    -> ElabCtx (S ctx) (S ctx')
bind (ElabCtx xs xs' ns v ts ts' rs ms ss cs s wk l pp) x x' a = ElabCtx
    { names   = xs :> x
    , names'  = xs' :> x'
    , nscope  = ns
    , values  = mapSink v :> t
    , types   = mapSink ts :> sink a
    , types'  = mapSink ts' :> sink a
    , rigids  = rigidMapSink (mapSink rs)
    , mtypes  = ms
    , stages  = ss :> cs
    , cstage  = cs
    , size    = SS s
    , wk      = KeepWk wk
    , loc     = l
    , doc     = pp
    }
  where
    t = evalZ s

bind'
    :: ElabCtx ctx ctx'
    -> Name                     -- ^ variable name
    -> EvalElim HasMetas ctx'   -- ^ value
    -> VTerm HasMetas ctx'      -- ^ type
    -> ElabCtx (S ctx) ctx'
bind' (ElabCtx xs xs' ns v ts ts' rs ms ss cs s wk l pp) x t a = ElabCtx
    { names   = xs :> x
    , names'  = xs'
    , nscope  = ns
    , values  = v :> t
    , types   = ts :> a
    , types'  = ts'
    , rigids  = rs
    , mtypes  = ms
    , stages  = ss :> cs
    , cstage  = cs
    , size    = s
    , wk      = SkipWk wk
    , loc     = l
    , doc     = pp
    }
