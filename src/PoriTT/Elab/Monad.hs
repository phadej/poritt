module PoriTT.Elab.Monad (
    ElabM,
    ElabState (..),
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
import PoriTT.Pruning
import PoriTT.Value
import PoriTT.Path
import PoriTT.Quote

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

-- TODO:
-- newMeta (Stage 0,PBind (PBind PEnd "A" (Stage 1) VUni) "x" (Stage 1) (VEmb (VRgd 0 VNil)))
--
-- Wrong:
-- newMeta VPie "A" Ecit VUni (Closure EmptyEnv (Pie "x" Ecit (Emb (Var 0)) (Cod (Quo Uni))))
-- forall (A : U) -> forall (x : A) -> Code [| A |]
--
-- Right:
-- forall (A : Code [| U |]) -> forall (x : Code A) -> Code A

newMeta :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (Elim HasMetas ctx)
newMeta ctx ty = do
    ty' <- either (throwError . fromString . show) return $ quoteTerm UnfoldNone ctx.size ty
    newMeta' ctx ty'

newMeta' :: ElabCtx ctx ctx' -> Term HasMetas ctx' -> ElabM (Elim HasMetas ctx)
newMeta' ctx ty0 = case ctx.qstage of
    NZ -> do
        -- traceM $ "newMeta " ++ show (ctx.cstage, ctx.path)

        (ty2, args) <- case closeType ctx.cstage ctx.path of
            Right (ty, args) -> return (ty ty0, args)
            Left err -> throwError $ fromString $ "cannot close type" ++ show err

        -- traceM $ "newMeta2 " ++ show ty2
        -- traceM $ "newMetaA " ++ show args
        m <- newMetaVar
        s <- get
        let ety = evalTerm SZ EmptyEnv ty2
        put $! s { metas = insertMetaMap m (Unsolved ety) s.metas }
        return (Met m (Qruning ctx.wk args))

    NS _q -> do
        res <- newMeta' (spliceElabCtx ctx) $ Cod $ Quo ty0
        return (Spl res)

solveMeta :: MetaVar -> VTerm HasMetas EmptyCtx -> ElabM (VTerm HasMetas EmptyCtx)
solveMeta m v = do
    -- traceM $ "SOLVE " ++ show m ++ " " ++ show v
    s <- get
    case lookupMetaMap m s.metas of
        Nothing              -> throwError $ "Unknown metavariable" <+> prettyMetaVar m
        Just (Solved _ty _v) -> throwError $ "Meta variable" <+> prettyMetaVar m <+> "is already solved:" -- TODO
        Just (Unsolved ty)   -> do
            put $! s
                { metas = insertMetaMap m (Solved ty v) s.metas
                }
            return ty

-------------------------------------------------------------------------------
-- Running elaboration monad
-------------------------------------------------------------------------------

evalElabM :: ElabM a -> Either Doc (MetaMap MetaEntry, a)
evalElabM m = case runExceptState m initialElabState of
    Left err     -> Left err
    Right (s, x) -> Right (s.metas, x)
