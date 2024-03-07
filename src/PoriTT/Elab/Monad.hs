module PoriTT.Elab.Monad (
    ElabM,
    ElabState (..), -- TODO
    Hole (..),
    newRigid,
    evalElabM,
) where

import PoriTT.Base
import PoriTT.PP
import PoriTT.Rigid
import PoriTT.ExceptState
import PoriTT.Name
import PoriTT.Value
import PoriTT.Term
import PoriTT.Elab.Ctx

type ElabM = ExceptState Doc ElabState

data ElabState = ElabState
    { rstate :: !RigidGen
    , holes  :: !(Map Name Hole)
    }
  deriving Generic

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

initialElabState :: ElabState
initialElabState = ElabState
    { rstate = initialRigidGen
    , holes  = mempty
    }

instance HasRigidGen ElabState where
    rigidGen = #rstate

newRigid :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (ElabCtx ctx ctx', RigidVar ctx')
newRigid ctx ty = do
    r <- newRigidVar
    return (ctx { rigids = insertRigidMap r ty ctx.rigids }, r)

evalElabM :: ElabM a -> Either Doc a
evalElabM m = evalExceptState m initialElabState
