module PoriTT.Elab.Monad (
    ElabM,
    newRigid,
) where

-- import PoriTT.Base

import PoriTT.PP
import PoriTT.Rigid
import PoriTT.ExceptState
import PoriTT.Value
import PoriTT.Term
import PoriTT.Elab.Ctx

type ElabM = ExceptState Doc RigidState

newRigid :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (ElabCtx ctx ctx', RigidVar ctx')
newRigid ctx ty = do
    r <- takeRigidVar
    return (ctx { rigids = insertRigidMap r ty ctx.rigids }, r)
