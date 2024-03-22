module PoriTT.Elab.Monad (
    ElabM,
    MetaEntry (..),
    metaEntryType,
    forceM,
    newRigid,
    newMeta,
    solveMeta,
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
import PoriTT.Quote
import PoriTT.Value
import PoriTT.Path

type ElabM = ExceptState Doc ElabState

data ElabState = ElabState
    { rigidGen :: !RigidGen
    , metaGen  :: !MetaGen -- for next  meta
    , metas    :: !(MetaMap MetaEntry)
    -- , holes  :: !(Map Name Hole)
    }
  deriving Generic

-- | During elaboration we don't only need to force globals,
-- but also metavariables.
forceM :: Size ctx -> VTerm HasMetas ctx -> ElabM (VTerm HasMetas ctx)
forceM size e = do
    s <- get
    return (force (forceTerm size s.metas e))

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
    , metaGen  = initialMetaGen
    , metas    = emptyMetaMap
    -- , holes  = mempty
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

instance HasMetaGen ElabState where
    metaGen = #metaGen

newMeta :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (Elim HasMetas ctx)
newMeta ctx ty0 = do
    let Right ty = closeType ctx.size ty0 ctx.path
    let Right ty' = quoteTerm UnfoldNone SZ ty
    m <- newMetaVar
    s <- get
    put $! s { metas = insertMetaMap m (Unsolved ty' ty) s.metas }
    return (closeElim (Met m) ctx.path)

solveMeta :: MetaVar -> Term HasMetas EmptyCtx -> VTerm HasMetas EmptyCtx -> ElabM ()
solveMeta m t v = do
    traceM $ "SOLVE " ++ show m ++ " " ++ show v
    s <- get
    case lookupMetaMap m s.metas of
        Nothing                  -> throwError $ "Unknown metavariable" <+> prettyMetaVar m
        Just (Solved _ _ty _ _v) -> throwError $ "Meta variable" <+> prettyMetaVar m <+> "is already solved:" -- TODO
        Just (Unsolved ty ty') -> put $! s
            { metas = insertMetaMap m (Solved ty ty' t v) s.metas
            }

-------------------------------------------------------------------------------
-- Running elaboration monad
-------------------------------------------------------------------------------

evalElabM :: ElabM a -> Either Doc (MetaMap MetaEntry, a)
evalElabM m = case runExceptState m initialElabState of
    Left err     -> Left err
    Right (s, x) -> Right (s.metas, x)
