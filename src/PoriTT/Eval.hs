module PoriTT.Eval (
    -- ** Closure
    run,
    runZ,
    runSTZ,
    runSEZ,
    runSE,
    -- * Evaluation
    evalTerm,
    evalElim,
    evalTerm',
    evalElim',
    force,
    -- ** Eliminations
    vapp,
    vapps,
    vappSpine,
    vappPruning,
    vappQruning,
    vsel,
    vswh,
    vdei,
    vind,
    vemb,
    vspl,
    vsplCodArg,
    -- ** Smart constructors
    vann,
    varr,
    vgbl,
    vcodUni,
    -- * Staging
    stageTerm,
    stageElim,
    -- * Eta expansions
    etaLam,
    -- * Quoting
    vquo,
) where

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Nice
import PoriTT.Pruning
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

import {-# SOURCE #-} PoriTT.Builtins (allTermGlobal, evalDescGlobal)

-------------------------------------------------------------------------------
-- VTerm and VElim
-------------------------------------------------------------------------------

-- | Force globals, when we need to pattern match on types.
force :: VTerm pass ctx -> VTerm pass ctx
force (VEmb (VGbl _ _ v)) = force (vemb v)
force v                   = v

-------------------------------------------------------------------------------
-- Closure
-------------------------------------------------------------------------------

run :: Size ctx -> ClosureT pass ctx -> VElim pass ctx -> VTerm pass ctx
run s (Closure env f) t = evalTerm' s (env :> velim t) f

-- | Run closure with (neutral) variable as an argument.
runZ :: Size ctx -> ClosureT pass ctx -> VTerm pass (S ctx)
runZ s (sink -> Closure env f) = evalTerm' (SS s) (env :> evalZ s) f

-------------------------------------------------------------------------------
-- Evaluation
-------------------------------------------------------------------------------

evalTerm :: Size ctx' -> EvalEnv pass ctx ctx' -> Term pass ctx -> VTerm pass ctx'
evalElim :: Size ctx' -> EvalEnv pass ctx ctx' -> Elim pass ctx -> VElim pass ctx'

evalTerm = evalTerm'
evalElim = evalElim'

evalTerm' :: Size ctx' -> EvalEnv pass ctx ctx' -> Term pass ctx -> VTerm pass ctx'
evalTerm' _ env (Lam x i t)   = VLam x i (Closure env t)
evalTerm' _ _   Uni           = VUni
evalTerm' _ _   One           = VOne
evalTerm' _ _   Tht           = VTht
evalTerm' _ _   Dsc           = VDsc
evalTerm' _ _   De1           = VDe1
evalTerm' s env (DeS t r)     = VDeS (evalTerm' s env t) (evalTerm' s env r)
evalTerm' s env (DeX t)       = VDeX (evalTerm' s env t)
evalTerm' s env (Muu t)       = VMuu (evalTerm' s env t)
evalTerm' s env (Con t)       = VCon (evalTerm' s env t)
evalTerm' s env (Pie x i a b) = VPie x i (evalTerm' s env a) (Closure env b)
evalTerm' s env (Sgm x i a b) = VSgm x i (evalTerm' s env a) (Closure env b)
evalTerm' s env (Emb e)       = vemb (evalElim' s env e)
evalTerm' _ _   (EIx i)       = VEIx i
evalTerm' _ _   (Fin ls)      = VFin ls
evalTerm' s env (Mul i t r)   = VMul i (evalTerm' s env t) (evalTerm' s env r)
evalTerm' s env (Cod a)       = VCod (evalTerm' s env a)
evalTerm' s env (Quo t)       = VQuo (stageTerm NZ s env t) (evalTerm' s env t)
evalTerm' s env (WkT w t)     = evalTerm' s (weakenEnv w env) t

evalElim' :: Size ctx' -> EvalEnv pass ctx ctx' -> Elim pass ctx -> VElim pass ctx'
evalElim' _ env (Var x)         = case lookupEnv x env of EvalElim v _ -> v
evalElim' s env (Met m xs)      = VFlx m (evalQruning s env xs)
evalElim' _ _   (Rgd _)         = TODO -- error?
evalElim' s _   (Gbl g)         = vgbl s g
evalElim' s env (Ann t a)       = vann (evalTerm' s env t) (evalTerm' s env a)
evalElim' s env (App i f t)     = vapp s i (evalElim' s env f) (evalTerm' s env t)
evalElim' s env (Sel e z)       = vsel s (evalElim' s env e) z
evalElim' s env (Swh e m ts)    = vswh s (evalElim' s env e) (evalTerm' s env m) (fmap (evalTerm' s env) ts)
evalElim' s env (DeI e m x y z) = vdei s (evalElim' s env e) (evalTerm' s env m) (evalTerm' s env x) (evalTerm' s env y) (evalTerm' s env z)
evalElim' s env (Ind e m t)     = vind s (evalElim' s env e) (evalTerm' s env m) (evalTerm' s env t)
evalElim' s env (Spl e)         = vspl s (evalElim' s env e)
evalElim' s env (Let _ t r)     = evalElim' s (env :> velim (evalElim' s env t)) r
evalElim' s env (WkE w e)       = evalElim' s (weakenEnv w env) e

evalPruning :: Size ctx' -> EvalEnv pass ctx ctx' -> Pruning ctx -> Spine pass ctx'
evalPruning _s env0 (Pruning xs) = go (weakenEnv xs env0) where
    go :: Env ctx1 (EvalElim pass ctx') -> Spine pass ctx'
    go EmptyEnv              = VNil
    go (env :> EvalElim e _) = VApp (go env) Ecit (vemb e)

evalQruning :: Size ctx' -> EvalEnv pass ctx ctx' -> Qruning ctx -> Spine pass ctx'
evalQruning _s env0 (Qruning xs qs0) = go (weakenEnv xs env0) qs0 where
    go :: Env ctx1 (EvalElim pass ctx') -> Env ctx1 Natural -> Spine pass ctx'
    go EmptyEnv               EmptyEnv   = VNil
    go (env :> EvalElim e e') (qs :> q )
        | q == 0    = VApp (go env qs) Ecit (vemb e)
        | otherwise = VApp (go env qs) Ecit (VQuo (SEmb e') (vemb e))

-------------------------------------------------------------------------------
-- Eliminations
-------------------------------------------------------------------------------

varr :: VTerm pass ctx -> Term pass Ctx1 -> VTerm pass ctx
varr a b = VPie "_" Ecit a (Closure EmptyEnv b)

vemb :: VElim pass ctx -> VTerm pass ctx
vemb (VAnn t _) = t
vemb e          = VEmb e

-- this reduction is not confluent, but we make more progress using
-- it -- and equate more things.
vann :: VTerm pass ctx -> VTerm pass ctx -> VElim pass ctx
vann (VEmb e) _ = e
vann t        s = VAnn t s

vgbl :: Size ctx -> Global -> VElim pass ctx
vgbl s g = VGbl g VNil (coeNoMetasVElim (sinkSize s g.val))

vapp :: Size ctx -> Icit -> VElim pass ctx -> VTerm pass ctx -> VElim pass ctx
vapp s _ (VAnn (VLam _ _ clos) (force -> VPie _ _ a b)) t =
    let t' = vann t a
    in vann (run s clos t') (run s b t')

vapp s i (VAnn (VEmb e) _) t = vapp s i e t
vapp _ _ (VAnn _ _)        _ = VErr EvalErrorApp
vapp _ i (VRgd l sp)       t = VRgd l (VApp sp i t)
vapp _ i (VFlx m sp)       t = VFlx m (VApp sp i t)
vapp s i (VGbl g sp h)     t = VGbl g (VApp sp i t) (vapp s i h t)
vapp _ _ (VErr msg)        _ = VErr msg

vapps :: Size ctx -> VElim pass ctx -> [VTerm pass ctx] -> VElim pass ctx
vapps s f xs = foldl' (vapp s Ecit) f xs

vappSpine :: Size ctx -> VElim pass ctx -> Spine pass ctx -> VElim pass ctx
vappSpine _ e VNil              = e
vappSpine s e (VApp sp i t)     = vapp s i (vappSpine s e sp) t
vappSpine s e (VSel sp r)       = vsel s (vappSpine s e sp) r
vappSpine s e (VSwh sp m ts)    = vswh s (vappSpine s e sp) m ts
vappSpine s e (VDeI sp m x y z) = vdei s (vappSpine s e sp) m x y z
vappSpine s e (VInd sp m t)     = vind s (vappSpine s e sp) m t
vappSpine s e (VSpl sp)         = vspl s (vappSpine s e sp)

vappPruning :: Size ctx -> VElim pass ctx -> Pruning ctx -> VElim pass ctx
vappPruning s e xs = vappSpine s e (evalPruning s (idEvalEnv s) xs)

vappQruning :: Size ctx -> VElim pass ctx -> Qruning ctx -> VElim pass ctx
vappQruning s e xs = vappSpine s e (evalQruning s (idEvalEnv s) xs)

-- vappPruning :: Size ctx -> VElim pass EmptyCtx -> Elim pass0 EmptyCtx

vsel :: Size ctx -> VElim pass ctx -> Selector -> VElim pass ctx
vsel s (VAnn (VMul _ t r) (force -> VSgm _ _ a b)) z
    | z == "fst"       = vann t a
    | z == "snd"       = vann r (run s b (vann t a))
    | otherwise        = VErr EvalErrorSel

vsel s (VAnn (VEmb e) _) z = vsel s e z
vsel _ (VAnn _ _)        _ = VErr EvalErrorSel
vsel _ (VRgd l sp)       t = VRgd l (VSel sp t)
vsel _ (VFlx m sp)       t = VFlx m (VSel sp t)
vsel s (VGbl g sp h)     t = VGbl g (VSel sp t) (vsel s h t)
vsel _ (VErr msg)        _ = VErr msg

vswh :: Size ctx -> VElim pass ctx -> VTerm pass ctx -> EnumList (VTerm pass ctx) -> VElim pass ctx
vswh s (VAnn i@(VEIx i') ty@(force -> VFin _)) m ts = case lookupEnumList i' ts of
    Just t  -> vann t $ vemb $ vapp s Ecit (vann m (varr ty Uni)) i
    Nothing -> VErr EvalErrorSwh
vswh s (VAnn (VEmb e) _) m ts = vswh s e m ts
vswh _ (VAnn _ _)        _ _  = VErr EvalErrorSwh
vswh _ (VRgd l sp)       m ts = VRgd l (VSwh sp m ts)
vswh _ (VFlx v sp)       m ts = VFlx v (VSwh sp m ts)
vswh s (VGbl g sp h)     m ts = VGbl g (VSwh sp m ts) (vswh s h m ts)
vswh _ (VErr msg)        _ _  = VErr msg

vdei :: Size ctx -> VElim pass ctx -> VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx -> VElim pass ctx
-- indDesc `1       M 1ₘ Σₘ Xₘ    = 1ₘ
vdei s (VAnn VDe1 (force -> VDsc)) m x _ _ = do
    let m' = vann m $ varr VDsc Uni
    let x' = vann x $ evalTerm' s (EmptyEnv :> velim m') descIndMotive1
    x'
-- indDesc (`Σ S D) M 1ₘ Σₘ Xₘ    = Σₘ S D (λ s → indDesc (D s) M 1ₘ Σₘ Xₘ)
vdei s (VAnn (VDeS t r) (force -> VDsc)) m x y z = do
    let m' = vann m $ varr VDsc Uni
    let x' = vann x $ evalTerm' s (EmptyEnv :> velim m') descIndMotive1
    let y' = vann y $ evalTerm' s (EmptyEnv :> velim m') descIndMotiveS
    let z' = vann z $ evalTerm' s (EmptyEnv :> velim m') descIndMotiveX
    let r' = vann r $ varr t Dsc
    vapps s y' [t, r, VLam "s" Ecit $ Closure (fmap velim (EmptyEnv :> m' :> x' :> y' :> z' :> r')) $ Emb $ DeI (var I1 @@ var IZ) (var I5) (var I4) (var I3) (var I2) ]

-- indDesc (`X D)   M 1ₘ Σₘ Xₘ    = Xₘ D (indDesc D M 1ₘ Σₘ Xₘ)
vdei s (VAnn (VDeX t) (force -> VDsc)) m x y z = do
    let m' = vann m $ varr VDsc Uni
    let z' = vann z $ evalTerm' s (EmptyEnv :> velim m') descIndMotiveX
    vapps s z' [t, vemb $ vdei s (vann t VDsc) m x y z]

vdei s (VAnn (VEmb e) _) m x y z = vdei s e m x y z
vdei _ (VAnn _ _)        _ _ _ _ = VErr EvalErrorDeI
vdei _ (VRgd l sp)       m x y z = VRgd l (VDeI sp m x y z)
vdei _ (VFlx v sp)       m x y z = VFlx v (VDeI sp m x y z)
vdei s (VGbl g sp h)     m x y z = VGbl g (VDeI sp m x y z) (vdei s h m x y z)
vdei _ (VErr msg)        _ _ _ _ = VErr msg

vind :: Size ctx -> VElim pass ctx -> VTerm pass ctx -> VTerm pass ctx -> VElim pass ctx
-- ind : {D : Desc}
--     → (x : μ D)
--     → (M : μ D → Set)
--     → (conₘ : (d : ⟦ D ⟧ (μ D)) → All D (μ D) M d → M (con d))
--     →  M x
-- ind {D} (con d) M conₘ = conₘ d (all D (μ D) M (λ x → ind x M conₘ) d)
vind s (VAnn (VCon d) (force -> VMuu dd)) m c = do
    let m'  = vann m  $ varr (VMuu d) Uni
    let dd' = vann dd VDsc
    let d'  = vann d (vemb (vapps s (vgbl s evalDescGlobal) [d, dd]))
    let c'  = vann c $ evalTerm' s (fmap velim (EmptyEnv :> dd' :> m')) muMotiveT
    evalElim' s (fmap velim (EmptyEnv :> dd' :> m' :> d' :> c')) $
        var IZ @@ var I1 @@ (Gbl allTermGlobal @@ var I3 @@ Muu (var I3) @@ var I2 @@ Lam "x" Ecit (Emb (Ind (var IZ) (var I3) (var I1))) @@ var I1)

vind s (VAnn (VEmb e) _) m t = vind s e m t
vind _ (VAnn _ _)       _ _ = VErr EvalErrorInd
vind _ (VRgd l sp)      m t = VRgd l (VInd sp m t)
vind _ (VFlx v sp)      m t = VFlx v (VInd sp m t)
vind s (VGbl g sp h)    m t = VGbl g (VInd sp m t) (vind s h m t)
vind _ (VErr msg)       _ _ = VErr msg

vspl :: Size ctx -> VElim pass ctx -> VElim pass ctx
vspl s (VAnn (VQuo _ t) (force -> VCod a)) = vann t (vsplCodArg s a)
vspl s (VAnn (VEmb e) _)                   = vspl s e
vspl _ (VAnn _ _)                          = VErr EvalErrorSpl
vspl _ (VRgd l sp)                         = VRgd l (VSpl sp)
vspl _ (VFlx m sp)                         = VFlx m (VSpl sp)
vspl s (VGbl _ _ h)                        = vspl s h -- VGbl g (VSpl sp) (vspl s h) -- we need a flag for unfold
vspl _ (VErr msg)                          = VErr msg

-- | @Code [| U |]@
vcodUni :: VTerm pass ctx
vcodUni = VCod (VQuo SUni VUni)

-- | @~(a : Code [| U |])@
vsplCodArg :: Size ctx -> VTerm pass ctx -> VTerm pass ctx
vsplCodArg s a = vemb (vspl s (vann a vcodUni))

-------------------------------------------------------------------------------
-- Staging
-------------------------------------------------------------------------------

stageTerm :: Natural -> Size ctx' -> EvalEnv pass ctx ctx' -> Term pass ctx -> STerm pass ctx'
stageTerm q s env (Pie x i a b) = SPie x i (stageTerm q s env a) (evalTerm s env a) (Closure env b)
stageTerm _ _ env (Lam x i t)   = SLam x i (Closure env t)
stageTerm q s env (Sgm x i a b) = SSgm x i (stageTerm q s env a) (Closure env b)
stageTerm q s env (Mul i t r)   = SMul i (stageTerm q s env t) (stageTerm q s env r)
stageTerm q s env (Cod t)       = SCod (stageTerm q s env t)
stageTerm q s env (Muu t)       = SMuu (stageTerm q s env t)
stageTerm q s env (Con t)       = SCon (stageTerm q s env t)
stageTerm q s env (Quo t)       = SQuo (stageTerm (NS q) s env t)
stageTerm _ _ _   Uni           = SUni
stageTerm _ _ _   One           = SOne
stageTerm _ _ _   Tht           = STht
stageTerm _ _ _   Dsc           = SDsc
stageTerm _ _ _   De1           = SDe1
stageTerm q s env (DeS t r)     = SDeS (stageTerm q s env t) (stageTerm q s env r)
stageTerm q s env (DeX t)       = SDeX (stageTerm q s env t)
stageTerm _ _ _   (Fin ls)      = SFin ls
stageTerm _ _ _   (EIx l)       = SEIx l
stageTerm q s env (Emb e)       = SEmb (stageElim q s env e)
stageTerm q s env (WkT w t)     = stageTerm q s (weakenEnv w env) t

sspl :: Size ctx -> SElim pass ctx -> VElim pass ctx -> SElim pass ctx
sspl _ _ (VAnn (VQuo (SEmb e') _) (force -> VCod (VQuo _ _))) = e'
sspl s _ (VAnn (VQuo t' _) (force -> VCod (VQuo a av))) = SAnn t' a (vsplCodArg s av)
sspl _ _ t@(VAnn _ _)                                     = SErr $ error $ show t
sspl s e (VGbl _ _ h)                                   = sspl s e h
sspl _ _ (VFlx h sp)                                    = SSpN (VNFlx h sp)
sspl _ _ (VRgd h sp)                                    = SSpN (VNRgd h sp)
sspl _ _ (VErr err)                                     = SErr err

stageElim :: Natural -> Size ctx' -> EvalEnv pass ctx ctx' -> Elim pass ctx -> SElim pass ctx'
stageElim _ _ env (Var x)   = case lookupEnv x env of
    EvalElim _ e -> e
stageElim _ _ _   (Met _m _)      = TODO -- not sure what to do here yet. should be an error
stageElim _ _ _   (Rgd _)         = TODO
stageElim _ _ _   (Gbl g)         = SGbl g
stageElim q s env (Swh e m ts)    = SSwh (stageElim q s env e) (stageTerm q s env m) (stageTerm q s env <$> ts)
stageElim q s env (Ann t a)       = SAnn (stageTerm q s env t) (stageTerm q s env a) (evalTerm s env a)
stageElim q s env (App i f t)     = SApp i (stageElim q s env f) (stageTerm q s env t) (evalTerm s env t)
stageElim q s env (Sel e r)       = SSel (stageElim q s env e) r
stageElim q s env (Let x a b)     = SLet x (stageElim q s env a) (Closure env b)
stageElim NZ     s env (Spl t)    = sspl s (stageElim NZ s env t) (evalElim' s env t)
stageElim (NS q) s env (Spl t)    = SSpl (stageElim q s env t) TODO -- (evalElim' s env t)
stageElim q s env (Ind e m t)     = SInd (stageElim q s env e) (stageTerm q s env m) (stageTerm q s env t)
stageElim q s env (DeI e m x y z) = SDeI (stageElim q s env e) (stageTerm q s env m) (stageTerm q s env x) (stageTerm q s env y) (stageTerm q s env z)
stageElim q s env (WkE w e)       = stageElim q s (weakenEnv w env) e

-- | Run closure with (neutral) variable as an argument.
runSTZ :: Natural -> Size ctx -> ClosureT pass ctx -> STerm pass (S ctx)
runSTZ q s (sink -> Closure env f) = stageTerm q (SS s) (env :> evalZ s) f

runSEZ :: Natural -> Size ctx -> ClosureE pass ctx -> SElim pass (S ctx)
runSEZ q s (sink -> Closure env f) = stageElim q (SS s) (env :> evalZ s) f

runSE :: Natural -> Size ctx -> ClosureE pass ctx -> EvalElim pass ctx -> SElim pass ctx
runSE q s (Closure env f) e = stageElim q s (env :> e) f

-------------------------------------------------------------------------------
-- Eta expansions
-------------------------------------------------------------------------------

-- | Eta expand value of function type.
etaLam :: Size ctx -> Icit -> VElim pass ctx -> VTerm pass (S ctx)
etaLam s i f = vemb (vapp (SS s) i (sink f) (vemb (valZ s)))

-------------------------------------------------------------------------------
-- Quoting
-------------------------------------------------------------------------------

vquo :: VTerm pass ctx -> VTerm pass ctx
-- TODO: experiment with commenting next line
vquo (VEmb (VRgd l (VSpl sp))) = VEmb (VRgd l sp)
-- vquo (VEmb e) = error $ "vquo: " ++ show e
vquo term = VQuo (auxT term) term
  where
    auxT :: VTerm pass ctx -> STerm pass ctx
    auxT VUni = SUni
    auxT (VPie x i a b) = SPie x i (auxT a) a b
    auxT (VEmb e)       = SEmb (auxE e)
    auxT VOne           = SOne
    auxT t' =  error $ "auxT: " ++ show t'

    auxE :: VElim pass ctx -> SElim pass ctx
    auxE (VRgd l VNil) = SVar l
    auxE (VRgd l sp) = auxSpine (SVar l) sp
    auxE e = error $ "auxE:" ++ show e

    auxSpine :: SElim pass ctx -> Spine pass ctx -> SElim pass ctx
    auxSpine h VNil = h
    auxSpine h (VApp sp i t) = SApp i (auxSpine h sp) (auxT t) t
    auxSpine h (VSpl sp) = SSpl (auxSpine h sp) (error "here2")
    auxSpine _ sp = error $ show sp
