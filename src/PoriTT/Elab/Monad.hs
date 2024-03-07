module PoriTT.Elab.Monad (
    ElabM,
    forceM,
    ElabState (..), -- TODO
    newRigid,
    evalElabM,
) where

import PoriTT.Base
import PoriTT.Elab.Ctx
import PoriTT.Eval
import PoriTT.ExceptState
import PoriTT.Meta
import PoriTT.PP
import PoriTT.Rigid
import PoriTT.Term
import PoriTT.Value

type ElabM = ExceptState Doc ElabState

data ElabState = ElabState
    { rigidGen :: !RigidGen
    -- , holes  :: !(Map Name Hole)
    -- , metaGen MetaGen -- for next  meta
    -- , mvalues  :: !(MetaMap (VTerm HasMetas EmptyCtx)
    }
  deriving Generic

-- | During elaboration we don't only need to force globals,
-- but also metavariables.
forceM :: VTerm HasMetas ctx -> ElabM (VTerm HasMetas ctx)
forceM t = return (force t) -- TODO

{-
data Hole where
    Hole
        :: VTerm HasMetas ctx'             -- ^ hole term, TODO: change to metavar?
        -> VTerm HasMetas ctx'             -- ^ hole type
        -> Size ctx'                       -- ^ size of ctx
        -> NameScope                       -- ^ namescope
        -> Env ctx Name                    -- ^ names in scope
        -> Env ctx' Name                   -- ^ names in output
        -> Env ctx (VTerm HasMetas ctx')   -- ^ types of variables in scope
        -> Hole
-}

initialElabState :: ElabState
initialElabState = ElabState
    { rigidGen = initialRigidGen
    -- , holes  = mempty
    -- , metaGen = initialMetaGen
    -- , mvalues = emptyMetaMap
    }

-------------------------------------------------------------------------------
-- Rigids
-------------------------------------------------------------------------------

instance HasRigidGen ElabState where
    rigidGen = #rigidGen

newRigid :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (ElabCtx ctx ctx', RigidVar ctx')
newRigid ctx ty = do
    r <- newRigidVar
    return (ctx { rigids = insertRigidMap r ty ctx.rigids }, r)

-------------------------------------------------------------------------------
-- Metas
-------------------------------------------------------------------------------

-- newMeta :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (ElabCtx ctx ctx', RigidVar ctx')

-------------------------------------------------------------------------------
-- Running elaboration monad
-------------------------------------------------------------------------------

evalElabM :: ElabM a -> Either Doc a
evalElabM m = evalExceptState m initialElabState
