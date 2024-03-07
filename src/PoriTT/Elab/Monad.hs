module PoriTT.Elab.Monad (
    ElabM,
    newRigid,
    evalElabM,
) where

import PoriTT.Base
import PoriTT.PP
import PoriTT.Rigid
import PoriTT.ExceptState
import PoriTT.Value
import PoriTT.Term
import PoriTT.Elab.Ctx

type ElabM = ExceptState Doc ElabState

data ElabState = ElabState
    { rstate :: !RigidState
    }
  deriving Generic

initialElabState :: ElabState
initialElabState = ElabState
    { rstate = initialRigidState
    }

instance HasRigidState ElabState where
    rigidState = #rstate

newRigid :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (ElabCtx ctx ctx', RigidVar ctx')
newRigid ctx ty = do
    r <- takeRigidVar
    return (ctx { rigids = insertRigidMap r ty ctx.rigids }, r)

evalElabM :: ElabM a -> Either Doc a
evalElabM m = evalExceptState m initialElabState
