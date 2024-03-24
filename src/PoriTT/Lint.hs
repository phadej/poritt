-- | By lint we mean re-typechecking of core terms.
module PoriTT.Lint (
    LintCtx (..),
    emptyLintCtx,
    lintTerm,
    lintElim,
) where

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Conv
import PoriTT.Enum
import PoriTT.Eval
import PoriTT.ExceptState
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Meta
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Rigid
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

-------------------------------------------------------------------------------
-- Linting context
-------------------------------------------------------------------------------

data LintCtx pass ctx ctx' = LintCtx
    { values :: EvalEnv pass ctx ctx'
    , types  :: Env ctx (VTerm pass ctx')
    , types' :: Env ctx' (VTerm pass ctx')
    , rigids :: !(RigidMap ctx' (VTerm pass ctx'))
    , stages :: Env ctx Stage
    , cstage :: Stage
    , names  :: Env ctx Name
    , names' :: Env ctx' Name
    , nscope :: NameScope
    , metas  :: MetaMap MetaEntry
    , size   :: Size ctx'
    , doc    :: ![Doc]
    }

toConvCtx :: LintCtx pass ctx ctx' -> ConvCtx pass ctx'
toConvCtx ctx = ConvCtx
    { size   = ctx.size
    , names  = ctx.names'
    , types  = ctx.types'
    , nscope = ctx.nscope
    , rigids = ctx.rigids
    , metas  = ctx.metas
    }

sinkLintCtx :: Name -> VTerm pass ctx' -> LintCtx pass ctx ctx' -> LintCtx pass ctx (S ctx')
sinkLintCtx x' t' (LintCtx vs ts ts' rs ss cs xs xs' ns ms s pp) = LintCtx (mapSink vs) (mapSink ts) (mapSink ts' :> sink t') (rigidMapSink (mapSink rs)) ss cs xs (xs' :> x') ns ms (SS s) pp

emptyLintCtx :: NameScope -> LintCtx pass EmptyCtx EmptyCtx
emptyLintCtx ns = LintCtx EmptyEnv EmptyEnv EmptyEnv emptyRigidMap EmptyEnv stage0 EmptyEnv EmptyEnv ns emptyMetaMap SZ []

bind :: LintCtx pass ctx ctx' -> Name -> Name -> VTerm pass ctx' -> LintCtx pass (S ctx) (S ctx')
bind ctx x x' a = define (sinkLintCtx x' a ctx) x (evalZ ctx.size) (sink a)

define :: LintCtx pass ctx ctx' -> Name -> EvalElim pass ctx' -> VTerm pass ctx' -> LintCtx pass (S ctx) ctx'
define (LintCtx vs ts ts' rs ss cs xs xs' ns ms s pp) x v t = LintCtx (vs :> v) (ts :> t) ts' rs (ss :> cs) cs (xs :> x) xs' ns ms s pp

weakenLintCtx :: Wk ctx ctx' -> LintCtx pass ctx' ctx'' -> LintCtx pass ctx ctx''
weakenLintCtx w (LintCtx vs ts ts' rs ss cs xs xs' ns ms s pp) = LintCtx (weakenEnv w vs) (weakenEnv w ts) ts' rs (weakenEnv w ss) cs (weakenEnv w xs) xs' ns ms s pp

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

type LintM = ExceptState Doc RigidGen

newRigid :: LintCtx pass ctx ctx' -> VTerm pass ctx' -> LintM (LintCtx pass ctx ctx', RigidVar ctx')
newRigid ctx ty = do
    r <- newRigidVar
    return (ctx { rigids = insertRigidMap r ty ctx.rigids }, r)

-------------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------------

lintError :: LintCtx pass ctx ctx' -> Doc -> [Doc] -> LintM a
lintError ctx msg extras = throwError $ ppHanging
    ("LINT:" <+> msg)
    [ ppBullet <+> e
    | e <- extras ++ ctx.doc
    ]

prettyVTermCtx :: LintCtx pass ctx ctx' -> VTerm pass ctx' -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names'

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

-- TODO

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

lintTerm
    :: LintCtx pass ctx ctx'           -- ^ Elaboration context
    -> Term pass ctx                   -- ^ Term
    -> VTerm pass ctx'                 -- ^ Expected type
    -> LintM ()
lintTerm ctx t a = do
    let d = "When checking that" <+> prettyTerm ctx.nscope ctx.names 0 t <+> "has type" <+> prettyVTermCtx ctx a
    lintTerm' ctx { doc = d : ctx.doc } t a

lintElim :: LintCtx pass ctx ctx' -> Elim pass ctx -> LintM (VTerm pass ctx')
lintElim ctx e = do
    let d = "When infering type of" <+> prettyElim ctx.nscope ctx.names 0 e
    lintElim' ctx { doc = d : ctx.doc } e

-------------------------------------------------------------------------------
-- Check & Infer
-------------------------------------------------------------------------------

lintIcit :: LintCtx pass ctx ctx' -> Icit -> Icit -> LintM ()
lintIcit ctx i j
    | i == j    = return ()
    | otherwise = lintError ctx "Icity mismatch"
        [ "expected:" <+> prettyIcit j
        , "actual:" <+> prettyIcit i
        ]

lintTerm' :: LintCtx pass ctx ctx' -> Term pass ctx -> VTerm pass ctx' -> LintM ()
lintTerm' ctx (Lam x i t)   (force -> VPie y j a b) = do
    --
    --  x : A ⊢ B ∋ t
    -- --------------------------------- lam
    --        ⊢ Π (x : A) → B ∋ λ x → t
    --
    lintIcit ctx i j
    let ctx' = bind ctx x y a
    lintTerm ctx' t (runZ ctx.size b)
lintTerm' ctx (Lam _ _ _)   ty   =
    lintError ctx "Lambda abstraction should have function type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (Pie x _i a b) (force -> VUni) = do
    --
    --        ⊢ U ∋ A
    --  x : A ⊢ U ∋ B
    -- --------------------------- pi
    --        ⊢ U ∋ Π (x : A) → B
    --
    lintTerm ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    lintTerm (bind ctx x x a') b VUni
lintTerm' ctx (Pie _ _ _ _) ty =
    lintError ctx "forall type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]
lintTerm' ctx (Sgm x _i a b) (force -> VUni) = do
    --
    --        ⊢ U ∋ A
    --  x : A ⊢ U ∋ B
    -- --------------------------- sigma
    --        ⊢ U ∋ Σ (x : A) × B
    --
    lintTerm ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    lintTerm (bind ctx x x a') b VUni
lintTerm' ctx (Sgm _ _ _ _) ty =
    lintError ctx "exists type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (Mul i t s) (force -> VSgm _ j a b) = do
    --
    -- ⊢ A ∋ t
    -- ⊢ B [z ↦ t] ∋ s
    -- ---------------------------- pair
    -- ⊢ Σ (z : A) × B ∋ pair t s
    --
    lintIcit ctx i j
    lintTerm ctx t a
    let tv = evalTerm ctx.size ctx.values t
    lintTerm ctx s (run ctx.size b (vann tv a))

lintTerm' ctx (Mul _ _ _) ty = do
    lintError ctx "pair constructor should have pair type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' _   One         (force -> VUni) =
    --
    --
    -- ------------ unit
    --  ⊢ U ∋ Unit
    --
    pure ()
lintTerm' ctx One ty   =
    lintError ctx "Unit should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' _   Tht         (force -> VOne) =
    --
    --
    -- ------------ tt
    --  ⊢ Unit ∋ tt
    --
    pure ()
lintTerm' ctx Tht ty   =
    lintError ctx "tt should have type Unit"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]


lintTerm' _ (Fin _) (force -> VUni) = do
    --
    -- ------------------- fin
    -- ⊢ U ∋ #[:a ... :z]
    --
  return ()

lintTerm' ctx (Fin _) ty =
    lintError ctx "finite set type should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (EIx i@(EnumIdx i')) (force -> VFin ls)
    --
    --  :l ∈ #[:a ... :z]
    -- ------------------ lbl
    -- ⊢ #[:a ... :z] ∋ :l
    --
    | i' < length ls
    = return ()

    | otherwise
    = lintError ctx ("enum index" <+> prettyEnumIdx i <+> "is larger than the cardinality of the set" <+> prettyVTermCtx ctx (VFin ls)) []

lintTerm' ctx (EIx _) ty   =
    lintError ctx "enum index should have a finite set type"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' _   Uni         (force -> VUni) =
    --
    --
    -- --------- type in type
    --  ⊢ U ∋ U
    --
    pure ()

lintTerm' ctx Uni         ty   =
    lintError ctx "U should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (Muu t)     (force -> VUni)= do
    --
    --  ⊢ Desc ∋ d
    -- ------------ mu
    --  ⊢ U ∋ μ d
    --
    lintTerm ctx t VDsc
lintTerm' ctx (Muu _)     ty =
    lintError ctx "mu should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (Con t)     (force -> ty@(VMuu d)) = do
    --
    --  ⊢ evalDesc d (μ d) ∋ t
    -- ------------------------ con
    --  ⊢ μ d ∋ con t
    --
    lintTerm ctx t (vemb (vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, ty]))

lintTerm' ctx (Con _)     ty =
    lintError ctx "con should have type mu"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' _   Dsc         (force -> VUni) =
    --
    --
    -- ------------ dsc
    --  ⊢ U ∋ Desc
    --
    pure ()

lintTerm' ctx Dsc         ty   =
    lintError ctx "Desc should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' _   De1         (force -> VDsc) =
    --
    --
    -- ------------- dsc-1
    --  ⊢ Desc ∋ `1
    --
    pure ()
lintTerm' ctx De1         ty =
    lintError ctx "`1 should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (DeS t s)   (force -> VDsc) = do
    --
    --  ⊢ U ∋ s
    --  ⊢ s -> Desc ∋ d
    -- ----------------- dsc-Σ
    --  ⊢ Desc ∋ `S s d
    --
    lintTerm ctx t VUni
    lintTerm ctx s (VPie "_" Ecit (evalTerm ctx.size ctx.values t) (Closure EmptyEnv Dsc))

lintTerm' ctx (DeS _ _)   ty =
    lintError ctx "`S should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (DeX t)   (force -> VDsc) =
    --
    --  ⊢ Desc ∋ d
    -- ----------------- dsc-X
    --  ⊢ Desc ∋ `X d
    --
    lintTerm ctx t VDsc

lintTerm' ctx (DeX _)   ty =
    lintError ctx "`X should have type Desc"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (Cod e)     (force -> VUni) =
    --
    --  ⊢ Code ⟦ U ⟧ ∋ A
    -- ------------------ code
    --  ⊢ U ∋ Code A
    --
    lintTerm ctx e vcodUni

lintTerm' ctx (Cod _)      ty   =
    lintError ctx "Code should have type U"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (Quo t)   (force -> VCod a) =
    --
    --  ⊢ ∫ (A : Code ⟦ U ⟧) ∋ t
    -- ---------------------------- quote
    --  ⊢ Code A ∋ ⟦ t ⟧
    --
    lintTerm ctx { cstage = pred ctx.cstage } t (vsplCodArg ctx.size a)

lintTerm' ctx (Quo _)   ty =
    lintError ctx "quote should have type Code"
        [ "actual:" <+> prettyVTermCtx ctx ty
        ]

lintTerm' ctx (Emb e)     a    = do
    --
    --  ⊢ e ∈ B
    --    A ≡ B
    -- --------- emb
    --  ⊢ A ∋ e
    --
    b <- lintElim ctx e
    case evalExceptState (convTerm (toConvCtx ctx) VUni a b) initialRigidGen of
        Right () -> pure ()
        Left err -> lintError ctx "Couldn't match types"
            [ "expected:" <+> prettyVTermCtx ctx a
            , "actual:" <+> prettyVTermCtx ctx b
            , err
            ]

lintTerm' ctx (WkT w t) a =
    lintTerm' (weakenLintCtx w ctx) t a

lintElim' :: forall pass ctx ctx'. LintCtx pass ctx ctx' -> Elim pass ctx -> LintM (VTerm pass ctx')
lintElim' ctx (Var x) = do
    --
    --  (x : A) ∈ Γ
    -- ------------- var
    --   Γ ⊢ x ∈ A
    --

    let s = lookupEnv x ctx.stages
    when (s /= ctx.cstage) $ do
        lintError ctx "Variable used at different stage"
            [ "variable:" <+> prettyName (lookupEnv x ctx.names)
            , "expected:" <+> prettyStage ctx.cstage
            , "actual:  " <+> prettyStage s
            ]

    return (lookupEnv x ctx.types)

lintElim' ctx (Gbl g) =
    -- Global is similar to variable.
    return (coeNoMetasVTerm (sinkSize ctx.size g.typ))

lintElim' ctx (Met m) = case lookupMetaMap m ctx.metas of
    Nothing -> lintError ctx "Unbound meta variable" [prettyMetaVar m]
    Just e  -> return (sinkSize ctx.size (metaEntryType e))

lintElim' ctx (Rgd _) =
    lintError ctx "Rigid variable" []

lintElim' ctx (App i f t) = do
    --
    --  ⊢ f ∈ Π (x : A) → B
    --  ⊢ A ∋ t
    -- --------------------- app
    --  ⊢ f t ∈ B [x ↦ t]
    --
    fty <- lintElim ctx f
    case force fty of
        VPie _ j a b -> do
            lintIcit ctx j i
            lintTerm ctx t a
            let t' = evalTerm ctx.size ctx.values t
            return (run ctx.size b (vann t' a))
        _ -> lintError ctx "Function application head is not pi-type"
            [ "actual:" <+> prettyVTermCtx ctx fty
            ]

lintElim' ctx (Sel e s) = do
    --
    --  ⊢ e ∈ Σ (z : A) × B
    -- --------------------- fst
    --  ⊢ e .fst ∈ A
    --
    --  ⊢ e ∈ Σ (z : A) × B
    -- ----------------------------- snd
    --  ⊢ e .snd ∈ B [ z ↦ e .fst ]
    --
    et <- lintElim ctx e
    case force et of
        -- for selectors we don't care about icity
        VSgm _ _i a b
            | s == "fst" -> return a
            | s == "snd" -> return (run ctx.size b (evalElim ctx.size ctx.values (Sel e "fst")))
            | otherwise  -> lintError ctx ("Sigma type doesn't have field" <+> prettySelector s) []

        _ -> lintError ctx "Selector application head does not have a selectable type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintElim' ctx (Swh e m ts) = do
    et <- lintElim ctx e
    case force et of
        VFin ls -> do
            unless (length ls == length ts) $ lintError ctx "Switch case arity mismatch"
                [ "actual:"   <+> ppInt (length ts)
                , "expected:" <+> ppInt (length ls) <+> ppParens (prettyVTermCtx ctx (VFin ls))
                ]

            -- {:ls...} -> U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            lintTerm ctx m mt
            let mv x = vemb (vapp ctx.size Ecit (vann (evalTerm ctx.size ctx.values m) mt) x)

            ifor_ ts $ \i t -> do
                lintTerm ctx t (mv (VEIx i))

            return (mv (vemb (evalElim ctx.size ctx.values e)))

        _ -> lintError ctx "Switch case scrutinee doesn't have finite set type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintElim' ctx (DeI e m c1 cS cX) = do
    --
    -- ⊢ e ∈ Desc
    -- ⊢ Desc → U ∋ M
    -- ⊢ M `1                                                          ∋ c1
    -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
    -- ⊢ Π (D : Desc) → M D → M (`X D)                                 ∋ cX
    ------------------------------------------------------------------------ desc-ind
    -- ⊢ indDesc e M c1 cS cX ∈ M e
    --

    -- ⊢ e ∈ Desc
    et <- lintElim ctx e
    case force et of
        VDsc -> do
            -- ⊢ Desc → U ∋ M
            let mt = evalTerm ctx.size EmptyEnv descIndMotive
            lintTerm ctx m mt

            let mv :: VElim pass ctx'
                mv = vann (evalTerm ctx.size ctx.values m) mt

            let mv' = velim mv

            -- ⊢ M `1 ∋ c1
            lintTerm ctx c1 $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotive1

            -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
            lintTerm ctx cS $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotiveS

            -- ⊢ Π (D : Desc) → M D → M (`X D) ∋ cX
            lintTerm ctx cX $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotiveX

            -- ... ∈ M e
            let ev = evalElim ctx.size ctx.values e
                ev' = velim ev
            return $ evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ)

        _ -> lintError ctx "Desc induction scrutinee doesn't have type Desc"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintElim' ctx (Ind e m t) = do
    --
    --  ⊢                                                      e ∈ μ D
    --  ⊢                                                μ D → U ∋ M
    --  ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
    -- ---------------------------------------------------------------- ind
    --  ⊢ ind e M t ∈ M e
    --

    -- ⊢ e ∈ μ D
    et <- lintElim ctx e
    case force et of
        VMuu d -> do
            -- ⊢ μ D → U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            lintTerm ctx m mt

            let mv :: VElim pass ctx'
                mv = vann (evalTerm ctx.size ctx.values m) mt

            let mv' = velim mv

            -- ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
            lintTerm ctx t $ evalTerm ctx.size (EmptyEnv :> velim (vann d VDsc) :> mv') muMotiveT

            -- ... ∈ M e
            let ev = evalElim ctx.size ctx.values e
                ev' = velim ev
            return $ evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ)

        _ -> lintError ctx "ind doesn't have type mu"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintElim' ctx (Ann t a) = do
    --
    --  ⊢ U ∋ A
    --  ⊢ A ∋ t
    -- --------------- ann
    --  ⊢ (t : A) ∈ A
    --
    lintTerm ctx a VUni
    let a' = evalTerm ctx.size ctx.values a
    lintTerm ctx t a'
    return a'

lintElim' ctx (Let x e f) = do
    --
    --  ⊢ e ∈ A
    --  ⊢ f [x ↦ e] ∈ B
    -- ---------------------- let
    --  ⊢ let x = e in f ∈ B
    --
    a <- lintElim ctx e
    (ctx', r) <- newRigid ctx a
    let e' = evalElim ctx.size ctx.values e
        e'' = EvalElim e' (SRgd r)
    lintElim (define ctx' x e'' a) f

lintElim' ctx (Spl e) = do
    --
    -- ⊢ e ∈ Code A
    -- ------------------------- splice
    -- ⊢ ∫e ∈ ∫(A : Code ⟦ U ⟧)
    --
    et <- lintElim ctx { cstage = succ ctx.cstage } e
    case force et of
        VCod a -> return (vsplCodArg ctx.size a)
        _ -> lintError ctx "Splice doesn't have type Code"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

lintElim' ctx (WkE w e) =
    lintElim' (weakenLintCtx w ctx) e
