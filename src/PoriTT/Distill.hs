module PoriTT.Distill (
    DistillCtx,
    emptyDistillCtx,
    DistillOpts (..),
    distillTerm,
    distillElim,
    prettierTerm,
    prettierElim,
    prettierElim',
) where

import qualified Data.Set as Set

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Conv
import PoriTT.Enum
import PoriTT.Eval
import PoriTT.ExceptState
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Raw
import PoriTT.Rigid
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

-------------------------------------------------------------------------------
-- Options
-------------------------------------------------------------------------------

data DistillOpts = DistillOpts
    { listPairUnit :: !Bool
    , listEnumFun  :: !Bool
    , conHeadEnum  :: !Bool
    , implicitApp  :: !Bool
    , implicitLam  :: !Bool
    }
  deriving (Show, Generic)

-------------------------------------------------------------------------------
-- Linting context
-------------------------------------------------------------------------------

-- TODO: add pass
data DistillCtx ctx ctx' = DistillCtx
    { values :: EvalEnv NoMetas ctx ctx'
    , types  :: Env ctx (VTerm NoMetas ctx')
    , types' :: Env ctx' (VTerm NoMetas ctx')
    , stages :: Env ctx Stage
    , cstage :: Stage
    , names  :: Env ctx Name
    , names' :: Env ctx' Name
    , nscope :: NameScope
    , size   :: Size ctx
    , size'  :: Size ctx'
    , opts   :: DistillOpts
    }

sinkDistillCtx :: Name -> VTerm NoMetas ctx' -> DistillCtx ctx ctx' -> DistillCtx ctx (S ctx')
sinkDistillCtx x' t' (DistillCtx vs ts ts' ss cs xs xs' ns s s' o) = DistillCtx (mapSink vs) (mapSink ts) (mapSink ts' :> sink t') ss cs xs (xs' :> x') ns s (SS s') o

emptyDistillCtx :: DistillOpts -> NameScope -> DistillCtx EmptyCtx EmptyCtx
emptyDistillCtx opts ns = DistillCtx EmptyEnv EmptyEnv EmptyEnv EmptyEnv stage0 EmptyEnv EmptyEnv ns SZ SZ opts

bind :: DistillCtx ctx ctx' -> Name -> Name -> VTerm NoMetas ctx' -> (Name, DistillCtx (S ctx) (S ctx'))
bind ctx x x' a = bind' (sinkDistillCtx x' a ctx) x (evalZ ctx.size') (sink a)

bind' :: DistillCtx ctx ctx' -> Name -> EvalElim NoMetas ctx' -> VTerm NoMetas ctx' -> (Name, DistillCtx (S ctx) ctx')
bind' (DistillCtx vs ts ts' ss cs xs xs' ns s s' o) x v t =
    withFreshName ns x $ \ns' x' ->
    (x', DistillCtx (vs :> v) (ts :> t) ts' (ss :> cs) cs (xs :> x') xs' ns' (SS s) s' o)

weakenDistillCtx :: Wk ctx ctx' -> DistillCtx ctx' ctx'' -> DistillCtx ctx ctx''
weakenDistillCtx w (DistillCtx vs ts ts' ss cs xs xs' ns s s' o) = DistillCtx (weakenEnv w vs) (weakenEnv w ts) ts' (weakenEnv w ss) cs (weakenEnv w xs) xs' ns (contractSize w s) s' o

distillError :: Maybe a
distillError = Nothing

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

prettierTerm :: DistillOpts -> NameScope -> Term NoMetas EmptyCtx -> VTerm NoMetas EmptyCtx -> Doc
prettierTerm opts ns t a = prettyRaw 0 (distillTerm (emptyDistillCtx opts ns) t a)

prettierElim :: DistillOpts -> NameScope -> Elim NoMetas EmptyCtx -> Doc
prettierElim opts ns e = prettyRaw 0 (distillElim (emptyDistillCtx opts ns) e)

prettierElim' :: DistillOpts -> NameScope -> Elim NoMetas EmptyCtx -> Doc
prettierElim' opts ns e = prettyRaw 0 (unRAnn (distillElim (emptyDistillCtx opts ns) e))

distillTerm
    :: DistillCtx ctx ctx'        -- ^ Elaboration context
    -> Term NoMetas ctx           -- ^ Term
    -> VTerm NoMetas ctx'         -- ^ Expected type
    -> Raw
distillTerm ctx t a = case distillTerm' ctx t a of
    Nothing -> toRaw ctx.nscope ctx.names t
    Just r  -> r

distillElim :: DistillCtx ctx ctx' -> Elim NoMetas ctx -> Raw
distillElim ctx e = case distillElim' ctx e of
    Nothing     -> toRaw ctx.nscope ctx.names e
    Just (r, _) -> r

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

-- | how terms
distillTerm' :: DistillCtx ctx ctx' -> Term NoMetas ctx -> VTerm NoMetas ctx' -> Maybe Raw
distillTerm' ctx (Lam _ Ecit (Emb (Swh (Var IZ) _p ts))) (force -> VPie _ _ (force -> VFin ls) b)
    | ctx.opts.listEnumFun
    , Just ts' <- traverse (renameA (unusedIdx ctx.size)) ts
    = fmap (RLst . toList) $ ifor ts' $ \i t ->
        distillTerm' ctx t $ run ctx.size' b (vann (VEIx i) (VFin ls))

distillTerm' ctx (Lam x i t) (force -> VPie y _ a b) = do
    let (x', ctx') = bind ctx x y a
    t' <- distillTerm' ctx' t (runZ ctx.size' b)
    return (distillLam ctx.opts x' i t')
distillTerm' _ (Lam _ _ _) _ =
    Nothing

distillTerm' ctx (Pie x i a b) (force -> VUni)
    | Just bb <- renameA (unusedIdx ctx.size) b
    , i == Ecit
    = do
        a' <- distillTerm' ctx a VUni
        b' <- distillTerm' ctx bb VUni
        return (RArr a' b')

    | otherwise = do
        a' <- distillTerm' ctx a VUni
        let av = evalTerm ctx.size' ctx.values a
        let (x', ctx') = bind ctx x x av
        b' <- distillTerm' ctx' b VUni
        return (RPie x' i a' b')
distillTerm' _ (Pie _ _ _ _) _ =
    Nothing

distillTerm' ctx (Sgm x i a b) (force -> VUni)
    | Just bb <- renameA (unusedIdx ctx.size) b
    , i == Ecit
    = do
        a' <- distillTerm' ctx a VUni
        b' <- distillTerm' ctx bb VUni
        return (RPrd a' b')

    | otherwise = do
        a' <- distillTerm' ctx a VUni
        let av = evalTerm ctx.size' ctx.values a
        let (x', ctx') = bind ctx x x av
        b' <- distillTerm' ctx' b VUni
        return (RSgm x' i a' b')
distillTerm' _ (Sgm _ _ _ _) _ =
    Nothing

distillTerm' ctx (Mul i t s) (force -> VSgm _ _ a b) = do
    a' <- distillTerm' ctx t a
    let tv = evalTerm ctx.size' ctx.values t
    b' <- distillTerm' ctx s (run ctx.size' b (vann tv a))
    return (distillMul ctx.opts i a' b')
distillTerm' _ (Mul _ _ _) _ = do
    Nothing

distillTerm' _ One (force -> VUni) =
    return ROne
distillTerm' _ One _   =
    Nothing

distillTerm' ctx Tht (force -> VOne) =
    return (distillTht ctx.opts)
distillTerm' _ Tht _ =
    Nothing

distillTerm' _ (Fin ls) (force -> VUni) = do
    return (RFin ls)
distillTerm' _ (Fin _) _ =
    Nothing

distillTerm' _ (EIx i) (force -> VFin ls)
    | Just m <- lookupLabel i ls
    = return (either RLbl REIx m)
    | otherwise
    = Nothing
distillTerm' _ (EIx _) _ =
    Nothing

distillTerm' _ Uni (force -> VUni) =
    pure RUni
distillTerm' _ Uni _ =
    Nothing

distillTerm' ctx (Muu t) (force -> VUni)= do
    t' <- distillTerm' ctx t VDsc
    return (RMuu t')
distillTerm' _ (Muu _) _ =
    Nothing

distillTerm' ctx (Con t) (force -> ty@(VMuu d)) = do
    t' <- distillTerm' ctx t (vemb (vapps ctx.size' (vgbl ctx.size' evalDescGlobal) [d, ty]))
    return (distillCon ctx.opts t')
distillTerm' _ (Con _) _ =
    Nothing

distillTerm' _ Dsc (force -> VUni) =
    return RDsc
distillTerm' _ Dsc _ =
    Nothing

distillTerm' _ De1 (force -> VDsc) =
    return RDe1
distillTerm' _ De1 _ =
    Nothing

distillTerm' ctx (DeS t s) (force -> VDsc) = do
    t' <- distillTerm' ctx t VUni
    s' <- distillTerm' ctx s (VPie "_" Ecit (evalTerm ctx.size' ctx.values t) (Closure EmptyEnv Dsc))
    return (RDeS t' s')
distillTerm' _ (DeS _ _) _ =
    Nothing

distillTerm' ctx (DeX t) (force -> VDsc) = do
    t' <- distillTerm' ctx t VDsc
    return (RDeX t')
distillTerm' _ (DeX _) _ =
    Nothing

distillTerm' ctx (Cod t) (force -> VUni) = do
    t' <- distillTerm' ctx t VUni
    return (RCod t' )
distillTerm' _ (Cod _) _ =
    Nothing

distillTerm' ctx (Quo t) (force -> VCod a) = do
    t' <- distillTerm' ctx { cstage = pred ctx.cstage } t a
    return (RQuo t')
distillTerm' _ (Quo _) _ =
    Nothing

distillTerm' ctx (Emb e) a = do
    (e', b) <- distillElim' ctx e
    case evalExceptState (convTerm (mkConvCtx ctx.size' ctx.names' ctx.types' ctx.nscope TODO) VUni a b) initialRigidGen of
        Right () -> pure e'
        Left _   -> Nothing

distillTerm' ctx (WkT w t) a =
    distillTerm' (weakenDistillCtx w ctx) t a

lookupLabel :: EnumIdx -> [Label] -> Maybe (Either Label EnumIdx)
lookupLabel (EnumIdx i) = go i Set.empty where
    go :: Int -> Set Label -> [Label] -> Maybe (Either Label EnumIdx)
    go _ _   []     = Nothing
    go 0 pfx (l:_)  = if Set.member l pfx then Just (Right (EnumIdx i)) else Just (Left l)
    go j pfx (l:ls) = go (j - 1) (Set.insert l pfx) ls

-- | Show eliminations.
distillElim' :: forall ctx ctx'. DistillCtx ctx ctx' -> Elim NoMetas ctx -> Maybe (Raw, VTerm NoMetas ctx')
distillElim' ctx (Var x)   = do
    let s = lookupEnv x ctx.stages
    when (s /= ctx.cstage) $ do
        Nothing

    return (RVar (lookupEnv x ctx.names), lookupEnv x ctx.types)

distillElim' ctx (Gbl g) =
    -- Global is similar to variable.
    return (RGbl g, sinkSize ctx.size' g.typ)

distillElim' _ctx (Rgd _) =
    Nothing

distillElim' ctx (App i f t) = do
    (f', fty) <- distillElim' ctx f
    case force fty of
        VPie _ _ a b -> do
            t' <- distillTerm' ctx t a
            let tv = evalTerm ctx.size' ctx.values t
            return (distillApp ctx.opts i f' t', run ctx.size' b (vann tv a))
        _ -> Nothing

distillElim' ctx (Sel e s) = do
    (e', et) <- distillElim' ctx e
    case force et of
        VSgm _ _ a b
            | s == "fst" -> return (rsel e' s, a)
            | s == "snd" -> return (rsel e' s, run ctx.size' b (evalElim ctx.size' ctx.values (Sel e "fst")))
            | otherwise  -> Nothing

        _ -> distillError

distillElim' ctx (Swh e m ts) = do
    (e', et) <- distillElim' ctx e
    case force et of
        VFin ls -> do
            -- TODO: check cardinality
            unless (length ls == length ts) distillError

            -- {:ls...} -> U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            m' <- distillTerm' ctx m mt
            let mv x = vemb (vapp ctx.size' Ecit (vann (evalTerm ctx.size' ctx.values m) mt) x)

            ts' <- ifor ts $ \i t -> do
                distillTerm' ctx t (mv (VEIx i))

            -- TODO!!!
            return
                ( RSwh e' m' $ ifoldr (\i t acc -> (maybe (error "TOOD") id (lookupLabel i ls) := t) : acc) [] ts'
                , mv (vemb (evalElim ctx.size' ctx.values e))
                )

        _ -> distillError

distillElim' ctx (DeI e m c1 cS cX) = do
    -- ⊢ e ∈ Desc
    (e', et) <- distillElim' ctx e
    case force et of
        VDsc -> do
            -- ⊢ Desc → U ∋ M
            let mt = evalTerm ctx.size' EmptyEnv descIndMotive
            m' <- distillTerm' ctx m mt

            let mv :: VElim NoMetas ctx'
                mv = vann (evalTerm ctx.size' ctx.values m) mt

                mv' = velim mv

            -- ⊢ M `1 ∋ c1
            c1' <- distillTerm' ctx c1 $ evalTerm ctx.size' (EmptyEnv :> mv') descIndMotive1

            -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
            cS' <- distillTerm' ctx cS $ evalTerm ctx.size' (EmptyEnv :> mv') descIndMotiveS

            -- ⊢ Π (D : Desc) → M D → M (`X D) ∋ cX
            cX' <- distillTerm' ctx cX $ evalTerm ctx.size' (EmptyEnv :> mv') descIndMotiveX

            -- ... ∈ M e
            let ev = evalElim ctx.size' ctx.values e
                ev' = velim ev
            return (RDeI e' m' c1' cS' cX', evalTerm ctx.size' (ctx.values :> mv' :> ev') (var I1 @@ var IZ))

        _ -> distillError

distillElim' ctx (Ind e m t) = do
    -- ⊢ e ∈ μ D
    (e', et) <- distillElim' ctx e
    case force et of
        VMuu d -> do
            -- ⊢ μ D → U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            m' <- distillTerm' ctx m mt

            let mv :: VElim NoMetas ctx'
                mv = vann (evalTerm ctx.size' ctx.values m) mt

                mv' = velim mv

            -- ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
            t' <- distillTerm' ctx t $ evalTerm ctx.size' (EmptyEnv :> velim (vann d VDsc) :> mv') muMotiveT

            -- ... ∈ M e
            let ev = evalElim ctx.size' ctx.values e
                ev' = velim ev
            return (RInd e' m' t', evalTerm ctx.size' (ctx.values :> mv' :> ev') (var I1 @@ var IZ))

        _ -> distillError

distillElim' ctx (Ann t a) = do
    a' <- distillTerm' ctx a VUni
    let av = evalTerm ctx.size' ctx.values a
    t' <- distillTerm' ctx t av
    return (RAnn t' a', av)

distillElim' ctx (Let x e f) = do
    (e', a) <- distillElim' ctx e
    let ev = evalElim ctx.size' ctx.values e
        ev' = velim ev -- TODO
    let (x', ctx') = bind' ctx x ev' a
    (f', b) <- distillElim' ctx' f
    return (RLet x' e' f', b)

distillElim' ctx (Spl e) = do
    (e', et) <- distillElim' ctx { cstage = succ ctx.cstage } e
    case force et of
        VCod a -> return (RSpl e', a)
        _      -> distillError

distillElim' ctx (WkE w e) =
    distillElim' (weakenDistillCtx w ctx) e

distillApp :: DistillOpts -> Icit -> Raw -> Raw -> Raw
distillApp opts i f t
    | not opts.implicitApp, i == Icit = f
    | otherwise                       = rapp i f t

distillLam :: DistillOpts -> Name -> Icit -> Raw -> Raw
distillLam opts x i t
    | not opts.implicitApp, i == Icit = t
    | otherwise                       = RLam x i t

distillMul :: DistillOpts -> Icit -> Raw -> Raw -> Raw
distillMul  opts Ecit t (RLst ss) | opts.listPairUnit = RLst (t:ss)
distillMul _opts i    t s                             = RMul i t s

distillTht :: DistillOpts -> Raw
distillTht  opts | opts.listPairUnit = RLst []
distillTht _opts                     = RTht

distillCon :: DistillOpts -> Raw -> Raw
distillCon  opts (RLst (RLbl l : ts)) | opts.conHeadEnum = rapps (RLbl l) ts
distillCon _opts r                                       = RCon r
