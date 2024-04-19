module PoriTT.Elab.Ctx (
    ElabCtx (..),
    bind,
    define,
    emptyElabCtx,
    quoteElabCtx,
    spliceElabCtx,
) where

import PoriTT.Base
import PoriTT.Loc
import PoriTT.Name
import PoriTT.PP
import PoriTT.Rigid
import PoriTT.Path
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
    , path   :: !(Path EmptyCtx ctx ctx')
    , stages :: !(Env ctx Stage)
    , cstage :: !Stage
    , qstage :: !Natural
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
    , path   = PEnd
    , stages = EmptyEnv
    , cstage = stage0
    , qstage = NZ
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
bind (ElabCtx xs xs' ns v ts ts' rs p ss cs qs s wk l pp) x x' a = ElabCtx
    { names   = xs :> x
    , names'  = xs' :> x'
    , nscope  = ns
    , values  = mapSink v :> t
    , types   = mapSink ts :> sink a
    , types'  = mapSink ts' :> sink a
    , rigids  = rigidMapSink (mapSink rs)
    , path    = PBind p x a
    , stages  = ss :> cs
    , cstage  = cs
    , qstage  = qs
    , size    = SS s
    , wk      = KeepWk wk
    , loc     = l
    , doc     = pp
    }
  where
    t = evalZ s

define
    :: ElabCtx ctx ctx'
    -> Name                     -- ^ variable name
    -> EvalElim HasMetas ctx'   -- ^ value
    -> VTerm HasMetas ctx'      -- ^ type
    -> ElabCtx (S ctx) ctx'
define (ElabCtx xs xs' ns v ts ts' rs p ss cs qs s wk l pp) x t a = ElabCtx
    { names   = xs :> x
    , names'  = xs'
    , nscope  = ns
    , values  = v :> t
    , types   = ts :> a
    , types'  = ts'
    , rigids  = rs
    , path    = PDefine p x
    , stages  = ss :> cs
    , cstage  = cs
    , qstage  = qs
    , size    = s
    , wk      = SkipWk wk
    , loc     = l
    , doc     = pp
    }

quoteElabCtx :: ElabCtx ctx ctx' -> ElabCtx ctx ctx'
quoteElabCtx ctx = ctx { cstage = succ ctx.cstage, qstage = NS ctx.qstage }

spliceElabCtx :: ElabCtx ctx ctx' -> ElabCtx ctx ctx'
spliceElabCtx ctx = ctx { cstage = pred ctx.cstage, qstage = predNat ctx.qstage }
