module PoriTT.Eval (
    -- ** Closure
    run,
    runZ,
    runSTZ,
    runSEZ,
    -- * Evaluation
    evalTerm,
    evalElim,
    evalTerm',
    evalElim',
    force,
    -- ** Eliminations
    vapp,
    vapps,
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
) where

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Nice
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

import {-# SOURCE #-} PoriTT.Builtins (allTermGlobal)

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
run s (Closure env f) t = evalTerm' s (env :> EvalElim t (SErr EvalErrorStg)) f

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
evalTerm' s env (Quo t)       = VQuo (stageTerm s env t) (evalTerm' s env t)
evalTerm' s env (WkT w t)     = evalTerm' s (weakenEnv w env) t

evalElim' :: Size ctx' -> EvalEnv pass ctx ctx' -> Elim pass ctx -> VElim pass ctx'
evalElim' _ env (Var x)       = case lookupEnv x env of EvalElim v _ -> v
evalElim' _ _ (Met _) = TODO
    -- TODO: we need metacontext.
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
    let d'  = vann d TODO
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
vspl s (VGbl _ _ h)                        = vspl s h -- VGbl g (VSpl sp) (vspl s h)
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

stageTerm :: Size ctx' -> EvalEnv pass ctx ctx' -> Term pass ctx -> STerm pass ctx'
stageTerm s env (Pie x i a b) = SPie x i (stageTerm s env a) (Closure env b)
stageTerm _ env (Lam x i t)   = SLam x i (Closure env t)
stageTerm s env (Sgm x i a b) = SSgm x i (stageTerm s env a) (Closure env b)
stageTerm s env (Mul i t r)   = SMul i (stageTerm s env t) (stageTerm s env r)
stageTerm s env (Cod t)       = SCod (stageTerm s env t)
stageTerm s env (Muu t)       = SMuu (stageTerm s env t)
stageTerm s env (Con t)       = SCon (stageTerm s env t)
stageTerm s env (Quo t)       = SQuo (stageTerm s env t)
stageTerm _ _   Uni           = SUni
stageTerm _ _   One           = SOne
stageTerm _ _   Tht           = STht
stageTerm _ _   Dsc           = SDsc
stageTerm _ _   De1           = SDe1
stageTerm s env (DeS t r)     = SDeS (stageTerm s env t) (stageTerm s env r)
stageTerm s env (DeX t)       = SDeX (stageTerm s env t)
stageTerm _ _   (Fin ls)      = SFin ls
stageTerm _ _   (EIx l)       = SEIx l
stageTerm s env (Emb e)       = SEmb (stageElim s env e)
stageTerm s env (WkT w t)     = stageTerm s (weakenEnv w env) t

stageElim :: Size ctx' -> EvalEnv pass ctx ctx' -> Elim pass ctx -> SElim pass ctx'
stageElim _ env (Var x)   = case lookupEnv x env of
    EvalElim _ e -> e
stageElim _ _   (Met _m)        = TODO -- not sure what to do here yet.
stageElim _ _   (Gbl g)         = SGbl g
stageElim s env (Swh e m ts)    = SSwh (stageElim s env e) (stageTerm s env m) (stageTerm s env <$> ts)
stageElim s env (Ann t a)       = SAnn (stageTerm s env t) (stageTerm s env a)
stageElim s env (App i f t)     = SApp i (stageElim s env f) (stageTerm s env t)
stageElim s env (Sel e r)       = SSel (stageElim s env e) r
stageElim s env (Let x a b)     = SLet x (stageElim s env a) (Closure env b)
stageElim s env (Spl t)         = SSpl (stageElim s env t) (vspl s $ evalElim' s env t)
stageElim s env (Ind e m t)     = SInd (stageElim s env e) (stageTerm s env m) (stageTerm s env t)
stageElim s env (DeI e m x y z) = SDeI (stageElim s env e) (stageTerm s env m) (stageTerm s env x) (stageTerm s env y) (stageTerm s env z)
stageElim s env (WkE w e)       = stageElim s (weakenEnv w env) e

-- | Run closure with (neutral) variable as an argument.
runSTZ :: Size ctx -> ClosureT pass ctx -> STerm pass (S ctx)
runSTZ s (sink -> Closure env f) = stageTerm (SS s) (env :> evalZ s) f

runSEZ :: Size ctx -> ClosureE pass ctx -> SElim pass (S ctx)
runSEZ s (sink -> Closure env f) = stageElim (SS s) (env :> evalZ s) f
