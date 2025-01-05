module PoriTT.Unify (
    UnifyEnv (..),
    unifyTerm,
) where

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Elab.Monad
import PoriTT.Enum
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Icit
import PoriTT.LvlMap
import PoriTT.Meta
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.PRen
import PoriTT.Quote
import PoriTT.Rigid
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

-------------------------------------------------------------------------------
-- Unification environment
-------------------------------------------------------------------------------

data UnifyEnv ctx = UnifyEnv
    { size   :: Size ctx
    , names  :: Env ctx Name
    , types  :: Env ctx (VTerm HasMetas ctx)
    , nscope :: NameScope
    , rigids :: RigidMap ctx (VTerm HasMetas ctx)
    }

bind :: Name -> VTerm HasMetas ctx -> UnifyEnv ctx -> UnifyEnv (S ctx)
bind x t (UnifyEnv s xs ts gs rs) = UnifyEnv (SS s) (xs :> x) (mapSink ts :> sink t) gs (rigidMapSink (mapSink rs))

makeClosure :: Size ctx -> VTerm 'HasMetas (S ctx) -> ClosureT HasMetas ctx
makeClosure s vt = case quoteTerm UnfoldNone (SS s) vt of
    Right t ->  Closure (tabulateEnv s $ \i -> let l = idxToLvl s i in EvalElim (VVar l) (SVar l)) t
    Left err -> error (show err)

newUnifyRigid :: UnifyEnv ctx -> VTerm HasMetas ctx -> ElabM (UnifyEnv ctx, RigidVar ctx)
newUnifyRigid ctx ty = do
    r <- newRigidVar
    return (ctx { rigids = insertRigidMap r ty ctx.rigids }, r)

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

prettyVTermCtx :: UnifyEnv ctx -> VTerm pass ctx -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names

prettySTermCtx :: Natural -> UnifyEnv ctx -> STerm pass ctx -> Doc
prettySTermCtx l ctx = prettySTerm l ctx.size ctx.nscope ctx.names

prettySElimCtx :: Natural -> UnifyEnv ctx -> SElim pass ctx -> Doc
prettySElimCtx l ctx = prettySElim l ctx.size ctx.nscope ctx.names

lookupLvl :: UnifyEnv ctx -> Lvl ctx -> Name
lookupLvl ctx l = lookupEnv (lvlToIdx ctx.size l) ctx.names

prettySpinePart :: UnifyEnv ctx -> Spine HasMetas ctx -> Doc
prettySpinePart ctx (VApp _sp Ecit v)  = "application" <+> prettyVTermCtx ctx v
prettySpinePart ctx (VApp _sp Icit v)  = "application" <+> ppBraces (prettyVTermCtx ctx v)
prettySpinePart _   (VSel _sp s)       = "selector" <+> prettySelector s
prettySpinePart _   (VSwh _sp _ _)     = "switch"
prettySpinePart _   (VDeI _sp _ _ _ _) = "indDesc"
prettySpinePart _   (VInd _sp _ _)     = "ind"
prettySpinePart _   (VSpl _sp)         = "splice"
prettySpinePart _   VNil               = "none"

-------------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------------

mismatch :: Doc -> Doc -> Doc -> ElabM a
mismatch t x y = throwError $ t <+> "mismatch:" <+> x <+> "/=" <+> y

notConvertible :: UnifyEnv ctx -> VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx -> ElabM a
notConvertible ctx ty x y = throwError $ ppSep
    [ "not convertible:"
    , prettyVTermCtx ctx ty <+> ":"
    , prettyVTermCtx ctx x <+> "/="
    , prettyVTermCtx ctx y
    ]

notConvertibleST :: Natural -> UnifyEnv ctx -> VTerm pass ctx -> STerm pass ctx -> STerm pass ctx -> ElabM a
notConvertibleST l ctx ty x y = throwError $ ppSep
    [ "not convertible (at level" <+> ppStr (show l) <> "):"
    , prettyVTermCtx ctx ty <+> ":"
    , prettySTermCtx l ctx x <+> "/="
    , prettySTermCtx l ctx y
    ]

notConvertibleSE :: Natural -> UnifyEnv ctx -> SElim pass ctx -> SElim pass ctx -> ElabM a
notConvertibleSE l ctx x y = throwError $ ppSep
    [ "not convertible (at level" <+> ppStr (show l) <> "):"
    , prettySElimCtx l ctx x <+> "/="
    , prettySElimCtx l ctx y
    -- , ppStr $ show x
    -- , ppStr $ show y
    ]

notType :: UnifyEnv ctx -> VTerm pass ctx -> ElabM a
notType ctx ty = throwError $ ppSep
    [ "CONV PANIC: NOT A TYPE"
    , prettyVTermCtx ctx ty
    ]

-------------------------------------------------------------------------------
-- Entry functions
-------------------------------------------------------------------------------

unifyTerm :: UnifyEnv ctx -> VTerm HasMetas ctx -> VTerm HasMetas ctx -> VTerm HasMetas ctx -> ElabM (VTerm HasMetas ctx)
unifyTerm env ty a b = do
    ty' <- forceM env.size ty
    a' <- forceM env.size a
    b' <- forceM env.size b
    -- traceM $ "unifyTerm " ++ show (ty', a', b')
    unifyTerm' env ty' a' b'

unifyElim :: UnifyEnv ctx -> VElim HasMetas ctx -> VElim HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
unifyElim env a b = do
    -- traceM $ "unifyElim " ++ show [a, b]
    unifyElim' env a b

-- | Beta-eta conversion checking of eliminations.
unifyNeut :: UnifyEnv ctx -> VNeut HasMetas ctx -> VNeut HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
unifyNeut ctx x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    unifyNeut' ctx x y

unifySTerm :: Natural -> UnifyEnv ctx -> VTerm HasMetas ctx -> STerm HasMetas ctx -> STerm HasMetas ctx -> ElabM (STerm HasMetas ctx)
unifySTerm l env ty a b = do
    ty' <- forceM env.size ty
    -- traceM $ "unifySTerm: " ++ show (ty', a, b)
    unifySTerm' l env ty' a b

unifySElim :: Natural -> UnifyEnv ctx -> SElim HasMetas ctx -> SElim HasMetas ctx -> ElabM (VTerm HasMetas ctx, SElim HasMetas ctx)
unifySElim l env a b = do
    -- traceM $ "unifySElim: " ++ show (a, b)
    unifySElim' l env a b

unifySTerm' :: Natural -> UnifyEnv ctx -> VTerm HasMetas ctx -> STerm HasMetas ctx -> STerm HasMetas ctx -> ElabM (STerm HasMetas ctx)
unifySTerm' l env    _       (SEmb x)           (SEmb y) =
    SEmb . snd <$> unifySElim l env x y

unifySTerm' _ _      VUni    SUni               SUni =
    return SUni
unifySTerm' _ _      VUni    SOne               SOne =
    return SOne
unifySTerm' l ctx    VUni    (SPie x i a1 av b1) (SPie _ j a2 _ b2) = do
    unifyIcit ctx i j
    a <- unifySTerm' l ctx VUni a1 a2
    _b <- unifySTerm' l (bind x av ctx) VUni (runSTZ l ctx.size b1) (runSTZ l ctx.size b2)
    return (SPie x i a av b1) -- (makeClosureS ctx.size b))
unifySTerm' l env ty@VUni    a                  b =
    notConvertibleST l env ty a b

-- TODO
unifySTerm' l env ty@VPie {} a                  b =
    notConvertibleST l env ty a b

-- TODO
unifySTerm' l env ty@VSgm {} a                  b =
    notConvertibleST l env ty a b

unifySTerm' _ _      VOne    STht               STht =
    return STht
unifySTerm' l env ty@VOne    a                  b =
    notConvertibleST l env ty a b

unifySTerm' _ _      (VFin _) (SEIx x)          (SEIx y)
    | x == y = return (SEIx x)
unifySTerm' l env ty@VFin {}  a                 b =
    notConvertibleST l env ty a b

-- TODO
unifySTerm' l env ty@VDsc {} a                  b =
    notConvertibleST l env ty a b

-- TODO
unifySTerm' l env ty@VMuu {} a                  b =
    notConvertibleST l env ty a b

-- TODO
unifySTerm' l env ty@VCod {} a                  b =
    notConvertibleST l env ty a b

unifySTerm' l env ty@VEmb {} a                  b =
    notConvertibleST l env ty a b

unifySTerm' _ ctx ty@VLam {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VDe1 {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VDeS {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VDeX {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VCon {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VMul {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VEIx {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VQuo {} _ _ = notType ctx ty
unifySTerm' _ ctx ty@VTht {} _ _ = notType ctx ty

unifySElim' :: Natural -> UnifyEnv ctx -> SElim HasMetas ctx -> SElim HasMetas ctx -> ElabM (VTerm HasMetas ctx, SElim HasMetas ctx)
unifySElim' _ _ (SErr err) _ = throwError $ ppStr $ show err
unifySElim' _ _ _ (SErr err) = throwError $ ppStr $ show err

unifySElim' _ env (SGbl x) (SGbl y)
    | x.name == y.name
    = return (sinkSize env.size (coeNoMetasVTerm x.typ), SGbl x)
unifySElim' l env a@SGbl {} b = notConvertibleSE l env a b

unifySElim' _ env (SVar x) (SVar y)
    | x == y
    = return (lookupEnv (lvlToIdx env.size x) env.types, SVar x)

    | otherwise
    = mismatch "variable" (prettyName (lookupLvl env x)) (prettyName (lookupLvl env y))
unifySElim' l env a@SVar {} b = notConvertibleSE l env a b

unifySElim' _      env (SSpN e1)   (SSpN e2) = do
    (e, ty) <- unifyNeut env e1 e2
    forceM env.size ty >>= \case
        VCod a -> return (vsplCodArg env.size a, SSpN $ TODO e)
        _ -> throwError ("splice argument does not have Code-type" <+> ppSep
            [ "actual:" <+> prettyVTermCtx env ty
            ])

unifySElim' l env a@SSpN {} b = notConvertibleSE l env a b

unifySElim' NZ     _env (SSpl _ _x) (SSpl _ _y) = do
    throwError "nope"
unifySElim' (NS l) env (SSpl e1 v) (SSpl e2 _) = do
    (ty, e)  <- unifySElim l env e1 e2
    return (vsplCodArg env.size ty, SSpl e v)

unifySElim' l env a@SSpl {} b = notConvertibleSE l env a b

unifySElim' l      ctx (SApp i f1 t1 v1) (SApp j f2 t2 _) = do
    unifyIcit ctx i j
    (ty, f) <- unifySElim l ctx f1 f2
    forceM ctx.size ty >>= \case
        VPie _ _i a b -> do
            t <- unifySTerm l ctx a t1 t2
            return (run ctx.size b (vann v1 ty), SApp i f t v1)
        _ -> throwError ("Function application head does not have a pi-type" <+> ppSep
            [ "actual:" <+> prettyVTermCtx ctx ty
            ])
unifySElim' l      env a@SApp {} b = notConvertibleSE l env a b

-- TODO
unifySElim' l      env a@SSel {} b = notConvertibleSE l env a b

-- TODO
unifySElim' l      env a@SDeI {} b = notConvertibleSE l env a b

-- TODO
unifySElim' l      env a@SInd {} b = notConvertibleSE l env a b

-- TODO
unifySElim' l      env a@SSwh {} b = notConvertibleSE l env a b

unifySElim' l      env (SLet x t1 s1) (SLet _ t2 s2) = do
    (ty, t) <- unifySElim' l env t1 t2
    (env', r) <- newUnifyRigid env ty
    let v = EvalElim (VErr TODO) (SRgd r)
    (ty', s) <- unifySElim l env' (runSE l env.size s1 v) (runSE l env.size s2 v)
    return (ty', SLet x t $ TODO s)

unifySElim' l      env a@SLet {} b = notConvertibleSE l env a b

unifySElim' _ env (SRgd x) (SRgd y)
    | x == y
    = case lookupRigidMap x env.rigids of
            Just ty -> return (ty, SRgd x)
            Nothing -> throwError ("rigid variable without a type")

unifySElim' l      env a@SRgd {} b = notConvertibleSE l env a b

unifySElim' l      env (SAnn t1 a1 v) (SAnn t2 a2 _) = do
    a <- unifySTerm l env VUni a1 a2
    t <- unifySTerm l env v    t1 t2
    return (v, SAnn t a v)
unifySElim' l      env a@SAnn {} b = notConvertibleSE l env a b



-------------------------------------------------------------------------------
-- Workers
-------------------------------------------------------------------------------

unifyIcit :: UnifyEnv ctx -> Icit -> Icit -> ElabM ()
unifyIcit _ctx i j
    | i == j    = return ()
    | otherwise = mismatch "icity" (prettyIcit i) (prettyIcit j)

unifyEmbTerm :: UnifyEnv ctx -> VElim HasMetas ctx -> VElim HasMetas ctx -> ElabM (VTerm HasMetas ctx)
unifyEmbTerm env x y = do
    (e, _ty) <- unifyElim env x y
    return (VEmb e)

unifyTerm' :: UnifyEnv ctx -> VTerm HasMetas ctx -> VTerm HasMetas ctx -> VTerm HasMetas ctx -> ElabM (VTerm HasMetas ctx)
unifyTerm' ctx (VEmb (VGbl _ _ t)) x y  = unifyTerm ctx (vemb t) x y
unifyTerm' ctx ty (VEmb (VGbl _ _ x)) y = unifyTerm ctx ty (vemb x) y
unifyTerm' ctx ty x (VEmb (VGbl _ _ y)) = unifyTerm ctx ty x (vemb y)

unifyTerm' ctx (VEmb (VAnn t _)) x y = unifyTerm' ctx t x y


-- ⊢ U ∋ t ≡ s
unifyTerm' _   VUni VUni             VUni =
    pure VUni
unifyTerm' _   VUni VDsc             VDsc =
    pure VDsc
unifyTerm' _   VUni VOne             VOne =
    pure VOne
unifyTerm' ctx VUni (VPie x i a1 b1) (VPie _ j a2 b2) = do
    unifyIcit ctx i j
    a <- unifyTerm ctx VUni a1 a2
    b <- unifyTerm (bind x a1 ctx) VUni (runZ ctx.size b1) (runZ ctx.size b2)
    return (VPie x i a (makeClosure ctx.size b))
unifyTerm' ctx VUni (VSgm x i a1 b1) (VSgm _ j a2 b2) = do
    unifyIcit ctx i j
    a <- unifyTerm ctx VUni a1 a2
    b <- unifyTerm (bind x a1 ctx) VUni (runZ ctx.size b1) (runZ ctx.size b2)
    return (VSgm x i a (makeClosure ctx.size b))
unifyTerm' ctx VUni (VMuu x)         (VMuu y) =
    VMuu <$> unifyTerm ctx VDsc x y
unifyTerm' _   VUni (VFin ls1)       (VFin ls2) =
    if ls1 == ls2
        then pure (VFin ls1)
    else mismatch "finite set" (prettyLabels ls1) (prettyLabels ls2)
unifyTerm' ctx VUni (VCod x)         (VCod y) =
    VCod <$> unifyTerm ctx vcodUni x y
unifyTerm' ctx VUni (VEmb e1)        (VEmb e2) =
    unifyEmbTerm ctx e1 e2
-- TBW comment: flex terms
unifyTerm' ctx VUni (VEmb (VFlx x sp)) t = do
    _ <- solve ctx x sp (vann t VUni)
    pure t
unifyTerm' ctx VUni t (VEmb (VFlx x sp)) = do
    _ <- solve ctx x sp (vann t VUni)
    pure t
unifyTerm' ctx VUni x                y              =
    notConvertible ctx VUni x y

-- ⊢ Π (x : A) → B ∋ t ≡ s
unifyTerm' ctx (VPie _ _ a b) (VLam x i t1)  (VLam _ j t2) = do
    unifyIcit ctx i j
    t <- unifyTerm (bind x a ctx) (runZ ctx.size b) (runZ ctx.size t1)  (runZ ctx.size t2)
    return (VLam x i (makeClosure ctx.size t))
unifyTerm' ctx (VPie _ _ a b) (VLam x i t1)  (VEmb v) = do
    t <- unifyTerm (bind x a ctx) (runZ ctx.size b) (runZ ctx.size t1)  (etaLam ctx.size i v)
    return (VLam x i (makeClosure ctx.size t))
unifyTerm' ctx (VPie _ _ a b) (VEmb u)       (VLam x i t2) = do
    t <- unifyTerm (bind x a ctx) (runZ ctx.size b) (etaLam ctx.size i u) (runZ ctx.size t2)
    return (VLam x i (makeClosure ctx.size t))
unifyTerm' ctx (VPie x i a b) (VEmb u)       (VEmb v) = do
    -- we need to eta expand, so we can unify singletons
    t <- unifyTerm (bind x a ctx) (runZ ctx.size b) (etaLam ctx.size i u) (etaLam ctx.size i v)
    return (VLam x i (makeClosure ctx.size t))
unifyTerm' ctx (VPie z i a b) x              y               =
    notConvertible ctx (VPie z i a b) x y

-- ⊢ Σ (z : A) × B ∋ t ≡ s
unifyTerm' ctx (VSgm _ _ a b) (VMul i t1 s1) (VMul j t2 s2) = do
    -- TODO: assert icity
    unifyIcit ctx i j
    t <- unifyTerm ctx a                           t1 t2
    s <- unifyTerm ctx (run ctx.size b (vann t a)) s1 s2
    return (VMul i t s)
unifyTerm' ctx (VSgm _ _ a b) (VMul i t1 s1) (VEmb q)       = do
    t <- unifyTerm ctx a                           t1 (vemb (vsel ctx.size q "fst"))
    s <- unifyTerm ctx (run ctx.size b (vann t a)) s1 (vemb (vsel ctx.size q "snd"))
    return (VMul i t s)
unifyTerm' ctx (VSgm _ _ a b) (VEmb p)       (VMul i t2 s2) = do
    t <- unifyTerm ctx a                           (vemb (vsel ctx.size p "fst")) t2
    s <- unifyTerm ctx (run ctx.size b (vann t a)) (vemb (vsel ctx.size p "snd")) s2
    return (VMul i t s)
unifyTerm' ctx (VSgm _ i a b) (VEmb p)       (VEmb q)       = do
    t <- unifyTerm ctx a                           (vemb (vsel ctx.size p "fst")) (vemb (vsel ctx.size q "fst"))
    s <- unifyTerm ctx (run ctx.size b (vann t a)) (vemb (vsel ctx.size p "snd")) (vemb (vsel ctx.size q "snd"))
    return (VMul i t s)
unifyTerm' ctx (VSgm z i a b) x              y              = notConvertible ctx (VSgm z i a b) x y

-- ⊢ Unit ∋ t ≡ s
unifyTerm' _   VOne      _            _            = pure VTht
-- TODO: unify (i.e. solve) flex metas with VTht

-- ⊢ {:a ... :z} ∋ t ≡ s
unifyTerm' _   (VFin ls) _            _
    -- eta expansion singletons: treat all elements equally
    | length ls == 1
    = pure (VEIx (EnumIdx 0))
unifyTerm' _   (VFin _)  (VEIx i1)    (VEIx i2)    =
    if i1 == i2
    then pure (VEIx i1)
    else mismatch "enum idx" (prettyEnumIdx i1) (prettyEnumIdx i2)
unifyTerm' ctx (VFin _)  (VEmb e1)    (VEmb e2) = do
    unifyEmbTerm ctx e1 e2
unifyTerm' ctx (VFin ls) x            y            =
    notConvertible ctx (VFin ls) x y

-- ⊢ Desc ∋ t ≡ s
unifyTerm' _   VDsc VDe1           VDe1           =
    pure VDe1
unifyTerm' ctx VDsc (VDeS t1 s1)   (VDeS t2 s2)   = do
    t <- unifyTerm ctx VUni t1 t2
    s <- unifyTerm ctx (VPie "S" Ecit t1 (Closure EmptyEnv Dsc)) s1 s2
    return (VDeS t s)
unifyTerm' ctx VDsc (VDeX t1)      (VDeX t2)      = do
    t <- unifyTerm ctx VDsc t1 t2
    return (VDeX t )
unifyTerm' ctx VDsc (VEmb e1)      (VEmb e2)      = do
    unifyEmbTerm ctx e1 e2
unifyTerm' ctx VDsc x              y              =
    notConvertible ctx VDsc x y

-- ⊢ μ d ∋ t ≡ s
unifyTerm' ctx (VMuu d) (VCon x)       (VCon y)     = do
    let xty = vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, VMuu d]
    t <- unifyTerm ctx (vemb xty) x y
    return (VCon t)
unifyTerm' ctx (VMuu _) (VEmb e1)      (VEmb e2)    = do
    unifyEmbTerm ctx e1 e2
unifyTerm' ctx (VMuu d) x              y            =
    notConvertible ctx (VMuu d) x y

-- ⊢ Code a ∋ t ≡ s
unifyTerm' ctx (VCod a) (VQuo t1 v1)     (VQuo t2 v2) = do
    let a' = vsplCodArg ctx.size a
    v <- unifyTerm ctx a' v1 v2
    t <- unifySTerm NZ ctx a' t1 t2
    return (VQuo t v)

unifyTerm' ctx (VCod _) (VEmb e1)      (VEmb e2)   = do
    unifyEmbTerm ctx e1 e2
unifyTerm' ctx (VCod a) x              y            = notConvertible ctx (VCod a) x y

-- Only neutral terms can be convertible under neutral type
unifyTerm' ctx (VEmb VRgd {})     (VEmb e1) (VEmb e2) = do
    unifyEmbTerm ctx e1 e2
unifyTerm' ctx (VEmb (VRgd h sp)) x y = notConvertible ctx (VEmb (VRgd h sp)) x y

unifyTerm' _   (VEmb (VErr msg)) _ _ = throwError $ ppStr $ show msg
unifyTerm' ctx ty@(VEmb (VFlx _ _)) _ _ = notType ctx ty

-- value constructors cannot be types
unifyTerm' ctx ty@VLam {} _ _ = notType ctx ty
unifyTerm' ctx ty@VDe1 {} _ _ = notType ctx ty
unifyTerm' ctx ty@VDeS {} _ _ = notType ctx ty
unifyTerm' ctx ty@VDeX {} _ _ = notType ctx ty
unifyTerm' ctx ty@VCon {} _ _ = notType ctx ty
unifyTerm' ctx ty@VMul {} _ _ = notType ctx ty
unifyTerm' ctx ty@VEIx {} _ _ = notType ctx ty
unifyTerm' ctx ty@VQuo {} _ _ = notType ctx ty
unifyTerm' ctx ty@VTht {} _ _ = notType ctx ty

-- | Unify eliminations
--
-- Return unified elimination and its type.
unifyElim' :: UnifyEnv ctx -> VElim HasMetas ctx -> VElim HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
-- Globals
unifyElim' env e@(VGbl g1 VNil _) (VGbl g2 VNil _)
    | g1.name == g2.name   = pure (e, coeNoMetasVTerm (sinkSize env.size g1.typ))
-- otherwise we check the values
unifyElim' ctx (VGbl _ _ t)   u             = unifyElim ctx t u
unifyElim' ctx t              (VGbl _ _ u)  = unifyElim ctx t u
unifyElim' ctx (VRgd h1 sp1)  (VRgd h2 sp2) = unifyRigidRigid ctx h1 sp1 h2 sp2
unifyElim' ctx (VAnn t ty)    e             = do
    t' <- unifyTerm ctx ty t (vemb e)
    return (VAnn t' ty, ty)
unifyElim' ctx e              (VAnn t ty)   = do
    t' <- unifyTerm ctx ty (vemb e) t
    return (VAnn t' ty, ty)
unifyElim' _   (VErr msg)     _             = throwError $ ppStr $ show msg
unifyElim' _   _              (VErr msg)    = throwError $ ppStr $ show msg
unifyElim' _   (VFlx _ _)     (VFlx _ _)    = throwError "flex-flex TODO"
unifyElim' env (VFlx m sp)    e             = solve env m sp e
unifyElim' env e              (VFlx m sp)   = solve env m sp e

unifyNeut' :: UnifyEnv ctx -> VNeut HasMetas ctx -> VNeut HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
-- Globals
unifyNeut' ctx (VNRgd h1 sp1)  (VNRgd h2 sp2) = unifyRigidRigid ctx h1 sp1 h2 sp2
unifyNeut' _   (VNErr msg)     _             = throwError $ ppStr $ show msg
unifyNeut' _   _              (VNErr msg)    = throwError $ ppStr $ show msg
unifyNeut' _   (VNFlx _ _)     _             = throwError "flex c"
unifyNeut' _   _              (VNFlx _ _)    = throwError "flex d"

-------------------------------------------------------------------------------
-- Rigid-Rigid
-------------------------------------------------------------------------------

unifyRigidRigid :: UnifyEnv ctx -> Lvl ctx -> Spine HasMetas ctx -> Lvl ctx -> Spine HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
unifyRigidRigid env x sp1 y sp2
    | x == y    = do
        -- traceM "convRigidRigid"
        -- traceM $ show $ prettyVTermCtx ctx (VRgd x sp1)
        -- traceM $ show $ prettyVTermCtx ctx (VRgd y sp2)
        -- traceM $ show $ prettyVTermCtx ctx headTy
        unifySpine env x sp1 sp2
    | otherwise = mismatch "spine head" (prettyName (lookupLvl env x)) (prettyName (lookupLvl env y))

unifySpine :: forall ctx. UnifyEnv ctx -> Lvl ctx -> Spine HasMetas ctx -> Spine HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
unifySpine ctx headLvl sp1' sp2' = do
    let len1 = spineLength sp1'
        len2 = spineLength sp2'

    unless (len1 == len2) $
        mismatch "spine length" (ppInt (spineLength sp1')) (ppInt (spineLength sp2'))

    go sp1' sp2'
  where
    headTy :: VTerm HasMetas ctx
    headTy = lookupEnv (lvlToIdx ctx.size headLvl) ctx.types

    go :: Spine HasMetas ctx -> Spine HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
    go VNil           VNil           =
        pure (VVar headLvl, headTy)
    go (VApp sp1 i t1) (VApp sp2 j t2) = do
        (h, ty) <- go sp1 sp2
        forceM ctx.size ty >>= \case
            VPie _ _ a b -> do
                unifyIcit ctx i j
                t <- unifyTerm ctx a t1 t2
                return (vapp ctx.size i h t, run ctx.size b (vann t a))

            _ -> TODO

    go (VSel sp1 s1) (VSel sp2 s2) = do
        (h, ty) <- go sp1 sp2
        unless (s1 == s2) $ mismatch "selector" (prettySelector s1) (prettySelector s2)
        forceM ctx.size ty >>= \case
            VSgm _ _ a b -> case s1 of
                "fst" -> return (vsel ctx.size h s1, a)
                "snd" -> return (vsel ctx.size h s1, run ctx.size b (vsel ctx.size h "fst"))
                _     -> throwError $ "conv panic: sigma with" <+> prettySelector s1

            _ -> TODO

    go (VSwh sp1 m1 xs) (VSwh sp2 m2 ys) = do
        (h, ty) <- go sp1 sp2
        unless (length xs == length ys) $ mismatch "switch case arity" (ppInt (length xs)) (ppInt (length ys))
        forceM ctx.size ty >>= \case
            VFin ls -> do
                m' <- unifyTerm ctx (VPie "_" Ecit (VFin ls) (Closure EmptyEnv Uni)) m1 m2
                let m :: VElim HasMetas ctx
                    m = vann m' $ varr (VFin ls) Uni

                zs <- ifor ls $ \i' l -> do
                    let i = EnumIdx i'
                    x <- maybe (throwError $ "missing case in throwError"  <+> prettyLabel l) return $ lookupEnumList i xs
                    y <- maybe (throwError $ "missing case in right" <+> prettyLabel l) return $ lookupEnumList i ys
                    unifyTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) (var IZ @@ EIx i)) x y

                return (vswh ctx.size h m' (makeEnumList zs), vemb (vapp ctx.size Ecit m (vemb h)))

            _ -> TODO

    go (VDeI sp1 m1 t1 s1 r1) (VDeI sp2 m2 t2 s2 r2) = do
        (h, ty) <- go sp1 sp2
        forceM ctx.size ty >>= \case
            VDsc -> do
                m' <- unifyTerm ctx (evalTerm ctx.size EmptyEnv         descIndMotive)  m1 m2
                let m :: VElim HasMetas ctx
                    m = vann m' $ varr VDsc Uni

                t <- unifyTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotive1) t1 t2
                s <- unifyTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotiveS) s1 s2
                r <- unifyTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotiveX) r1 r2

                return (vdei ctx.size h m' t s r, vemb (vapp ctx.size Ecit m (vemb h)))

            _ -> TODO

    go (VInd sp1 m1 c1) (VInd sp2 m2 c2) = do
        (h, ty) <- go sp1 sp2
        forceM ctx.size ty >>= \case
            VMuu d -> do
                m' <- unifyTerm ctx (VPie "_" Ecit (VMuu d) (Closure EmptyEnv Uni))  m1 m2
                let m :: VElim HasMetas ctx
                    m = vann m' $ varr (VMuu d) Uni

                    d' :: VElim HasMetas ctx
                    d' = vann d VDsc

                c <- unifyTerm ctx (evalTerm ctx.size (EmptyEnv :> velim d' :> velim m) muMotiveT) c1 c2
                return (vind ctx.size h m' c, vemb (vapp ctx.size Ecit m (vemb h)))

            _ -> TODO

    go (VSpl sp1) (VSpl sp2) = do
        (h, ty) <- go sp1 sp2
        forceM ctx.size ty >>= \case
            VCod a ->
                return (vspl ctx.size h, vsplCodArg ctx.size a)

            _ -> TODO

    go x y =
        throwError $ "last eliminator mismatch" <+> prettySpinePart ctx x <+> "/=" <+> prettySpinePart ctx y

-------------------------------------------------------------------------------
-- Flex-Rigid
-------------------------------------------------------------------------------

-- TODO: return Env ctx' Icit
data Invert ctx where
    -- TODO: add Names ctx'
    Invert :: Size ctx' -> Env ctx' Name -> PRen ctx ctx' -> Invert ctx

deriving instance Show (Invert ctx)

--  invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ
invert :: UnifyEnv ctx -> Spine HasMetas ctx -> ElabM (Invert ctx)
invert env VNil             = return (Invert SZ EmptyEnv (emptyLvlMap env.size))
invert env (VApp sp Ecit t) = do
    Invert s' names pren <- invert env sp
    t' <- forceM env.size t
    case t' of
        VEmb (VVar l) -> case lookupLvlMap l pren of
            -- TODO: i'm not sure if we want lvlZ or lvlTop?
            Nothing -> return $ Invert (SS s') (names :> lookupLvl env l) (insertLvlMap l (lvlZ s') (mapSink pren))
            Just _  -> throwError $ "non-linear spine" <+> prettyVTermCtx env t'

        _ -> throwError $ "non-variable spine element" <+> prettyVTermCtx env t'

invert env sp = throwError $ "cannot invert " <+> prettySpinePart env sp

{-

invert :: Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl)
      go []        = pure (0, mempty)
      go (sp :> t) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren


{-
Wrap a term in lambdas.
-}
lams :: Lvl -> Tm -> Tm
lams l = go 0 where
  go x t | x == l = t
  go x t = Lam ("x"++show (x+1)) $ go (x + 1) t

--       Γ      ?α         sp       rhs
solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  rhs  <- rename m pren rhs
  let solution = eval [] $ lams (dom pren) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved solution)

-}

-- TODO: take icits
-- TODO: take type (name)
sizeLams :: Size ctx -> Env ctx Name -> Term HasMetas ctx -> Term HasMetas EmptyCtx
sizeLams SZ     _            t = t
sizeLams (SS s) (names :> n) t = sizeLams s names (Lam n Ecit t)

solve :: UnifyEnv ctx -> MetaVar -> Spine HasMetas ctx -> VElim HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
solve env m sp rhs = do
    Invert s' names' pren <- invert env sp
    rhs' <- either throwError return $ prenTerm (PRenEnv env.size s' pren m) (vemb rhs)
    traceM $ show $ prettyTerm env.nscope names' 0 rhs'
    let rhs'' = sizeLams s' names' rhs'
    traceM $ show $ prettyTerm env.nscope EmptyEnv 0 rhs''
    let rhs''' = evalTerm SZ EmptyEnv rhs''
    mty <- solveMeta m rhs'''
    vappType env (sinkSize env.size (vann rhs''' mty)) (sinkSize env.size mty) sp

-- TODO: take size, don't use monad, move to eval
vappType :: UnifyEnv ctx -> VElim HasMetas ctx -> VTerm HasMetas ctx -> Spine HasMetas ctx -> ElabM (VElim HasMetas ctx, VTerm HasMetas ctx)
vappType _   h ty VNil = pure (h, ty)
vappType env h ty (VApp sp i t) = do
    (h', ty') <- vappType env h ty sp
    case ty' of
        VPie _y _j a b ->
            return (vapp env.size i h' t, run env.size b (vann t a))

        _ -> TODO
vappType env h ty sp = error (show sp) env h ty
