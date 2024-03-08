-- | Type-checking.
--
-- We do some type-directed elaboration: desugaring list syntax,
-- but nothing which needs unification
module PoriTT.Elab (
    ElabCtx,
    emptyElabCtx,
    ElabM,
    evalElabM,
    elabTerm,
    elabElim,
) where

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Conv
import PoriTT.Elab.Ctx
import PoriTT.Elab.Monad
import PoriTT.Enum
import PoriTT.Eval
import PoriTT.ExceptState
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Loc
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Rigid
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Unify
import PoriTT.Used
import PoriTT.Value
import PoriTT.Well

-------------------------------------------------------------------------------
-- Unification
-------------------------------------------------------------------------------

toUnifyEnv :: ElabCtx ctx ctx' -> UnifyEnv ctx'
toUnifyEnv ctx = UnifyEnv
    { size   = ctx.size
    , names  = ctx.names'
    , types  = ctx.types'
    , nscope = ctx.nscope
    , rigids = ctx.rigids
    }

unify
    :: ElabCtx ctx ctx'
    -> VTerm HasMetas ctx'
    -> VTerm HasMetas ctx'
    -> VTerm HasMetas ctx'
    -> ElabM (VTerm HasMetas ctx') 
unify ctx ty t s = do
    case evalExceptState (convTerm (ConvCtx ctx.size ctx.names' ctx.types' ctx.nscope ctx.rigids) ty t s) initialRigidGen of
        Right () -> pure t
        Left err -> elabError ctx "Couldn't unify terms"
            [ "expected:" <+> prettyVTermCtx ctx s
            , "actual:" <+> prettyVTermCtx ctx t
            , err
            ]

-------------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------------

elabError :: ElabCtx ctx ctx' -> Doc -> [Doc] -> ElabM a
elabError ctx msg extras = throwError $ elabError' ctx msg extras

elabError' :: ElabCtx ctx ctx' -> Doc -> [Doc] -> Doc
elabError' ctx msg extras = ppHanging
    (prettyLoc ctx.loc <> ":" <+> msg)
    [ ppBullet <+> ppAlign e
    | e <- extras ++ take 5 ctx.doc
    ]

notType :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (Term HasMetas ctx)
notType ctx ty = elabError ctx "Checking against non-type"
    [ "not-type:" <+> prettyVTermCtx ctx ty
    ]

invalidTerm :: ElabCtx ctx ctx' -> Doc -> VTerm HasMetas ctx' -> Well (HasTerms HasMetas) ctx -> ElabM (Term HasMetas ctx)
invalidTerm ctx cls ty t = elabError ctx ("Checking against" <+> cls)
    [ "type:" <+> prettyVTermCtx ctx ty
    , "term:" <+> prettyWell ctx.nscope ctx.names 0 t
    ]

prettyVTermCtx :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names'

prettyNamesTypes :: Size ctx' -> NameScope -> Env ctx' Name -> Env ctx Name -> Env ctx (VTerm HasMetas ctx') -> [Doc]
prettyNamesTypes _ _  _   EmptyEnv  EmptyEnv  =  []
prettyNamesTypes s ns env (xs :> x) (ts :> t) =
    (prettyName x <+> ":" <+> t') :
    prettyNamesTypes s ns env xs ts
  where
    t' = case quoteTerm UnfoldElim s t of
        Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
        Right n  -> prettyTerm ns env 0 n

-------------------------------------------------------------------------------
-- insertion
-------------------------------------------------------------------------------

-- | Insert implicit arguments for as long as there are in type.
insert :: ElabCtx ctx ctx'
    -> (Elim HasMetas ctx, VTerm HasMetas ctx')
    -> ElabM (Elim HasMetas ctx, VTerm HasMetas ctx')
insert _ x = return x

-------------------------------------------------------------------------------
-- Check & Infer wrappers
-------------------------------------------------------------------------------

-- | Check term ('Term') against a type (as 'VTerm').
elabTerm
    :: ElabCtx ctx ctx'               -- ^ Type checking context
    -> Well (HasTerms HasMetas) ctx     -- ^ Well scoped term
    -> VTerm HasMetas ctx'              -- ^ Expected type
    -> ElabM (Term HasMetas ctx)   -- ^ Type checked term
elabTerm ctx t a = do
    let d = ppSep
            [ "When checking that"
            , prettyWell ctx.nscope ctx.names 0 t
            , "has type"
            , prettyVTermCtx ctx a
            ]
    elabTerm' ctx { doc = d : ctx.doc } t a

-- | Infer type of an elimination ('Elim').
elabElim
    :: ElabCtx ctx ctx'                                   -- ^ Type checking context
    -> Well (HasTerms HasMetas) ctx                         -- ^ Well scoped elimination
    -> ElabM (Elim HasMetas ctx, VTerm HasMetas ctx')   -- ^ Type checked elimination and its type
elabElim ctx e = do
    let d = ppSep
            [ "When infering type of"
            , prettyWell ctx.nscope ctx.names 0 e
            ]
    elabElim' ctx { doc = d : ctx.doc } e

-------------------------------------------------------------------------------
-- Check helpers
-------------------------------------------------------------------------------

elabIcit :: ElabCtx ctx ctx' -> Icit -> Icit -> ElabM ()
elabIcit ctx i j
    | i == j    = return ()
    | otherwise = elabError ctx "Icity mismatch"
        [ "expected:" <+> prettyIcit j
        , "actual:" <+> prettyIcit i
        ]

elabHole :: ElabCtx ctx ctx' -> Name -> VTerm HasMetas ctx' -> ElabM (Term HasMetas ctx)
elabHole ctx n ty = elabError ctx ("Checking a hole" <+> prettyHole n) $
    [ "type:" <+> prettyVTermCtx ctx ty
    ] ++
    (prettyNamesTypes ctx.size ctx.nscope ctx.names' ctx.names ctx.types)

elabSkipped :: ElabCtx ctx ctx' -> VTerm HasMetas ctx' -> ElabM (Term HasMetas ctx)
elabSkipped ctx ty = do
    m <- newMeta ctx ty
    return (Emb (Met m))

elabInfer :: ElabCtx ctx ctx' -> Well (HasTerms HasMetas) ctx -> VTerm HasMetas ctx' -> ElabM (Term HasMetas ctx)
elabInfer ctx e            a = do
    (e', et) <- elabElim ctx e
    -- traceM $ "CONV: " ++ show (ctx.names', e, et, a)
    _ <- unify ctx VUni a et
    return (Emb e')

elabLabel :: ElabCtx ctx ctx' -> Label -> [Label] -> ElabM EnumIdx
elabLabel ctx l0 ls0 = go 0 ls0 where
    go :: Int -> [Label] -> ElabM EnumIdx
    go !_ [] = elabError ctx ("label" <+> prettyLabel l0 <+> "is not in the set" <+> prettyVTermCtx ctx (VFin ls0)) []
    go !i (l:ls)
        | l == l0   = return (EnumIdx i)
        | otherwise = go (i + 1) ls

checkEnumIdx :: ElabCtx ctx ctx' -> EnumIdx -> [Label] -> ElabM EnumIdx
checkEnumIdx ctx i@(EnumIdx i') ls0
    | i' < length ls0 = return i
    | otherwise = elabError ctx ("enum index " <+> prettyEnumIdx i <+> "is out of bounds of" <+> prettyVTermCtx ctx (VFin ls0)) []

-- TODO: Better name for this.
foo :: ElabCtx ctx ctx' -> [Label] -> [Either Label EnumIdx := a] -> ElabM (EnumList a)
foo ctx ls0 m0 = go 0 [] m0 ls0 where
    go _ tgt src []
        | null src  = return $ makeEnumList $ reverse tgt
        | otherwise = elabError ctx "switch map contains extra keys"
            [ ppStr (show (map fst src))
            ]

    go i' tgt src (l:ls)
        | Just (x, src') <- lookupRemoving (Left l) src
        = go (i' + 1) (x : tgt) src' ls

        | Just (x, src') <- lookupRemoving (Right i) src
        = go (i' + 1) (x : tgt) src' ls

        | otherwise
        = elabError ctx "switch map doesn't contain a key"
            [ "missing:" <+> prettyLabel l <+> "or" <+> prettyEnumIdx i
            , "keys:" <+> ppStr (show (map fst src))
            ]
      where
        i = EnumIdx i'

lookupRemoving :: Eq a => a -> [(a,b)] -> Maybe (b, [(a,b)])
lookupRemoving k = go id where
    go _pfx []         = Nothing
    go  pfx ((x,y):zs)
        | x == k       = Just (y, pfx zs)
        | otherwise    = go (pfx . ((x,y) :)) zs

-------------------------------------------------------------------------------
-- Check term
-------------------------------------------------------------------------------

elabTerm'
    :: ElabCtx ctx ctx'                -- ^ Type checking context
    -> Well (HasTerms HasMetas) ctx      -- ^ Well scoped term
    -> VTerm HasMetas ctx'               -- ^ Expected type
    -> ElabM (Term HasMetas ctx)    -- ^ Type checked term
elabTerm' ctx (WLoc l t) ty = elabTerm' ctx { loc = l } t ty
elabTerm' ctx (WHol n)   ty = elabHole ctx n ty
elabTerm' ctx WSkp       ty = elabSkipped ctx ty
elabTerm' ctx e@WVar {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WGbl {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WApp {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WSel {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WSwh {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WDeI {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WInd {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WSpl {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WAnn {}  ty = elabInfer ctx e ty
elabTerm' ctx e@WLet {}  ty = elabInfer ctx e ty
elabTerm' ctx t          ty = forceM ty >>= \ty' -> elabTerm'' ctx ty' t

elabTerm''
    :: ElabCtx ctx ctx'               -- ^ Type checking context
    -> VTerm HasMetas ctx'              -- ^ Expected type
    -> Well (HasTerms HasMetas) ctx     -- ^ Well scoped term
    -> ElabM (Term HasMetas ctx)   -- ^ Type checked term
elabTerm'' ctx (VEmb (VErr msg)) _t = do
    elabError ctx "Type evaluation error"
        [ ppStr (show msg)
        ]

-- types
elabTerm'' _ctx VUni WUni = return Uni
elabTerm'' _ctx VUni WOne = return One
elabTerm'' _ctx VUni WDsc = return Dsc
elabTerm'' _ctx VUni (WFin ls) = return (Fin ls)
elabTerm''  ctx VUni (WPie x i a b) = do
    a' <- elabTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- elabTerm (bind ctx x x av) b VUni
    return (Pie x i a' b')
elabTerm'' ctx VUni (WSgm x i a b) = do
    a' <- elabTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- elabTerm (bind ctx x x av) b VUni
    return (Sgm x i a' b')
elabTerm'' ctx VUni (WMuu t) = do
    t' <- elabTerm ctx t VDsc
    return (Muu t')
elabTerm'' ctx VUni (WCod t) = do
    t' <- elabTerm ctx t vcodUni
    return (Cod t')
elabTerm'' ctx ty@VUni t = do
    invalidTerm ctx "U" ty t

-- functions
elabTerm'' ctx (VPie y i a b) (WLam x j t) = do
    elabIcit ctx i j
    let ctx' = bind ctx x y a
    t' <- elabTerm ctx' t (runZ ctx.size b)
    return (Lam x i t')
{-
elabTerm'' ctx (VPie x Ecit (force -> VFin ls) b) (WLst ts) = do
    TODO
-}
elabTerm'' ctx ty@(VPie _ _ _ _) t =
    invalidTerm ctx "Pi-type" ty t

-- pairs
elabTerm'' ctx (VSgm _ j a b) (WMul i t s) = do
    elabIcit ctx i j
    t' <- elabTerm' ctx t a
    let tv = evalTerm ctx.size ctx.values t'
    s' <- elabTerm ctx s (run ctx.size b (vann tv a))
    return (Mul i t' s')
elabTerm'' ctx (VSgm x Ecit a b) (WLst ts0) = do
    --
    -- ⊩ Σ (x : A) × B ∋ t , [s...] ▹ r
    -- --------------------------------
    -- ⊩ Σ (x : A) × B ∋ [ t s...] ▹ r
    --
    case ts0 of
        [] -> elabError ctx
            "Null list expression checked against sigma type"
            []
        t:ts -> do
            elabTerm ctx (WMul Ecit t (WLst ts)) (VSgm x Ecit a b)
elabTerm'' ctx ty@(VSgm _ _ _ _) t =
    invalidTerm ctx "Sigma-type" ty t

-- unit
elabTerm'' _ctx VOne WTht =
    return Tht
elabTerm'' ctx VOne (WLst ts) = do
    --
    -- ------------------
    -- ⊩ Unit ∋ [] ▹ tt
    --
    when (not (null ts)) $ elabError ctx
        "Non-null list expression checked against enum type"
        []
    return Tht
elabTerm'' ctx ty@VOne t =
    invalidTerm ctx "Unit" ty t

-- descriptions
elabTerm'' _ctx VDsc WDe1 =
    return De1
elabTerm'' ctx VDsc (WDeS t s) = do
    t' <- elabTerm ctx t VUni
    s' <- elabTerm ctx s (VPie "_" Ecit (evalTerm ctx.size ctx.values t') (Closure EmptyEnv Dsc))
    return (DeS t' s')
elabTerm'' ctx VDsc (WDeX t) = do
    t' <- elabTerm ctx t VDsc
    return (DeX t')
elabTerm'' ctx ty@VDsc t =
    invalidTerm ctx "Description" ty t

-- fixed points
elabTerm'' ctx ty@(VMuu d) (WCon t) = do
    t' <- elabTerm ctx t $ vemb $ vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, ty]
    return (Con t')
elabTerm'' ctx (VMuu (force -> VDeS (force -> VFin ls) d)) (WLbl l ts) = do
    --
    -- ⊩ #E ∋ :c ▹ n
    -- ⊩ evalDesc ((D : #E → Desc) n) (μ (`Σ E# D)) ∋ [t...] ▹ t'
    -- ------------------------------------------------------------
    -- ⊩ μ (`Σ #E D) ∋ :c t... ▹ con (n , t')
    --
    i' <- elabLabel ctx l ls
    let d' = vann d (VPie "_" Ecit (VFin ls) (Closure EmptyEnv Dsc))
    t' <- elabTerm ctx (WLst ts) $ vemb $ vapps ctx.size (vgbl ctx.size evalDescGlobal)
        [ vemb (vapp ctx.size Ecit d' (VEIx i'))
        , VMuu (VDeS (VFin ls) d)
        ]

    return $ Con (Mul Ecit (EIx i') t')

elabTerm'' ctx ty@(VMuu _) t =
    invalidTerm ctx "Mu-type" ty t

-- finite enumerations
elabTerm'' ctx (VFin ls) (WLbl l ts) = do
    unless (null ts) $ elabError ctx
        ("label" <+> prettyLabel l <+> "is applied to arguments but checked against finite set type")
        []
    i' <- elabLabel ctx l ls
    return (EIx i')
elabTerm'' ctx (VFin ls) (WEIx i ts) = do
    unless (null ts) $ elabError ctx
        ("enum index " <+> prettyEnumIdx i <+> "is applied to arguments but checked against finite set type")
        []
    i' <- checkEnumIdx ctx i ls
    return (EIx i')
elabTerm'' ctx ty@(VFin _) t =
    invalidTerm ctx "finite enumeration" ty t

-- code
elabTerm'' ctx (VCod a) (WQuo t) = do
    t' <- elabTerm ctx { cstage = pred ctx.cstage } t (vsplCodArg ctx.size a)
    return (Quo t')
elabTerm'' ctx ty@(VCod _) t =
    invalidTerm ctx "Code" ty t

-- not types
elabTerm'' ctx ty@VLam {} _ = notType ctx ty
elabTerm'' ctx ty@VDe1 {} _ = notType ctx ty
elabTerm'' ctx ty@VDeS {} _ = notType ctx ty
elabTerm'' ctx ty@VDeX {} _ = notType ctx ty
elabTerm'' ctx ty@VCon {} _ = notType ctx ty
elabTerm'' ctx ty@VMul {} _ = notType ctx ty
elabTerm'' ctx ty@VEIx {} _ = notType ctx ty
elabTerm'' ctx ty@VQuo {} _ = notType ctx ty
elabTerm'' ctx ty@VTht {} _ = notType ctx ty

-- emb ann should be reduced, but we don't enforce that.
elabTerm'' ctx (VEmb (VAnn ty _))  t = elabTerm'' ctx ty t

-- force
elabTerm'' ctx (VEmb (VGbl _ _ v)) t = elabTerm'' ctx (vemb v) t

elabTerm'' ctx (VEmb ty@(VRgd _ _)) _ =
    elabError ctx "Cannot check against neutral-type"
        [ "type:" <+> prettyVTermCtx ctx (VEmb ty)
        ]

elabTerm'' ctx ty@(VEmb (VFlx _ _)) t = elabInfer ctx t ty

-------------------------------------------------------------------------------
-- Check Elim
-------------------------------------------------------------------------------

elabElim' :: forall ctx ctx'. ElabCtx ctx ctx' -> Well (HasTerms HasMetas) ctx -> ElabM (Elim HasMetas ctx, VTerm HasMetas ctx')
elabElim' ctx (WLoc l r)
    = elabElim' ctx { loc = l } r
elabElim' ctx (WVar i) = do
    let s = lookupEnv i ctx.stages
    when (s /= ctx.cstage) $ do
        elabError ctx "Variable used at different stage"
            [ "variable:" <+> prettyName (lookupEnv i ctx.names)
            , "expected:" <+> prettyStage ctx.cstage
            , "actual:  " <+> prettyStage s
            ]

    pure (Var i, lookupEnv i ctx.types)
elabElim' ctx (WGbl g) =
    pure (Gbl g, coeNoMetasVTerm (sinkSize ctx.size g.typ))
elabElim' ctx (WHol n) =
    elabError ctx
    ("Cannot infer type of a hole" <> prettyHole n)
    []
elabElim' ctx WSkp =
    elabError ctx
    ("Cannot infer type of skipped term")
    []
elabElim' ctx (WLam _ _ _) =
    elabError ctx
    "Cannot infer type of a lambda abstraction"
    []
elabElim' ctx (WMul _ _ _) =
    elabError ctx
    "Cannot infer type of a pair constructor"
    []
elabElim' ctx (WCon _) =
    elabError ctx
    "Cannot infer type of a con constructor"
    []
elabElim' ctx (WLbl _ _) =
    elabError ctx
    "Cannot infer type of a label"
    []
elabElim' ctx (WEIx _ _) =
    elabError ctx
    "Cannot infer type of an enum index"
    []
elabElim' ctx (WQuo _) =
    elabError ctx
    "Cannot infer type of a quote"
    []
elabElim' ctx (WLst _) =
    elabError ctx
    "Cannot infer type of a list expression"
    []
elabElim' ctx (WPie x i a b) = do
    a' <- elabTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- elabTerm (bind ctx x x av) b VUni
    return (Ann (Pie x i a' b') Uni, VUni)
elabElim' ctx (WSgm x i a b) = do
    a' <- elabTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- elabTerm (bind ctx x x av) b VUni
    return (Ann (Sgm x i a' b') Uni, VUni)
elabElim' _   (WFin ls) =
    return (Ann (Fin ls) Uni, VUni)
elabElim' _   WUni =
    return (Ann Uni Uni, VUni)
elabElim' _   WOne =
    return (Ann One Uni, VUni)
elabElim' _   WTht =
    return (Ann Tht One, VOne)
elabElim' _   WDsc =
    return (Ann Dsc Uni, VUni)
elabElim' _   WDe1 =
    return (Ann De1 Dsc, VDsc)
elabElim' ctx (WDeX t) = do
    t' <- elabTerm ctx t VDsc
    return (Ann (DeX t') Dsc, VDsc)
elabElim' ctx (WDeS t s) = do
    t' <- elabTerm ctx t VUni
    let tv = evalTerm ctx.size ctx.values t'
    s' <- elabTerm ctx s (VPie "_" Ecit tv (Closure EmptyEnv Dsc))
    return (Ann (DeS t' s') Dsc, VDsc)
elabElim' ctx (WMuu t) = do
    t' <- elabTerm ctx t VDsc
    return (Ann (Muu t') Uni, VUni)
elabElim' ctx (WCod a) = do
    a' <- elabTerm ctx a vcodUni
    return (Ann (Cod a') Uni, VUni)
elabElim' ctx (WApp i f t) = do
    (f', ft) <- elabElim ctx f
    case force ft of
        VPie _ j a b -> do
            elabIcit ctx j i
            t' <- elabTerm ctx t a
            let tv = evalTerm ctx.size ctx.values t'
            return (App i f' t', run ctx.size b (vann tv a))
        _ -> elabError ctx "Function application head does not have a pi-type"
            [ "actual:" <+> prettyVTermCtx ctx ft
            ]
elabElim' ctx (WSel e s) = do
    (e', et) <- elabElim ctx e
    case force et of
        VSgm _ _i a b
            | s == "fst" -> return (Sel e' s, a)
            | s == "snd" -> return (Sel e' s, run ctx.size b (evalElim ctx.size ctx.values (Sel e' "fst")))
            | otherwise  -> elabError ctx ("Sigma type doesn't have field" <+> prettySelector s) []

        -- TODO: pie with a ~ WFin
        _ -> elabError ctx "Selector application head does not have a selectable type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

elabElim' ctx (WSwh e m ts) = do
    (e', et) <- elabElim ctx e
    case force et of
        VFin ls -> do
            ts0 <- foo ctx ls ts

            -- {:ls...} -> U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            m' <- elabTerm ctx m mt
            let mv :: VElim HasMetas ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

                mv' = velim mv

            -- in { :l -> t }
            -- M :l ∋ t
            ts' <- ifor ts0 $ \i t -> do
                elabTerm ctx t $ evalTerm ctx.size (EmptyEnv :> mv') (var IZ @@ EIx i)

            let ev = evalElim ctx.size ctx.values e'
                ev' = velim ev
            return (Swh e' m' ts', evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ))

        _ -> elabError ctx "Switch case scrutinee doesn't have finite set type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

elabElim' ctx (WDeI e m c1 cS cX) = do
    -- ⊢ e ∈ Desc
    (e', et) <- elabElim ctx e
    case force et of
        VDsc -> do
            -- ⊢ Desc → U ∋ M
            let mt = evalTerm ctx.size EmptyEnv descIndMotive
            m' <- elabTerm ctx m mt
            let mv :: VElim HasMetas ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

                mv' = velim mv

            -- ⊢ M `1 ∋ c1
            c1' <- elabTerm ctx c1 $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotive1

            -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
            cS' <- elabTerm ctx cS $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotiveS

            -- ⊢ Π (D : Desc) → M D → M (`X D) ∋ cX
            cX' <- elabTerm ctx cX $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotiveX

            -- ∈ M e
            let ev = evalElim ctx.size ctx.values e'
                ev' = velim ev

            return
              ( DeI e' m' c1' cS' cX'
              , evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ)
              )

        _ -> elabError ctx "Desc induction scrutinee doesn't have type Desc"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

elabElim' ctx (WInd e m t) = do
    -- ⊢ e ∈ μ D
    (e', et) <- elabElim ctx e
    case force et of
        VMuu d -> do
            -- ⊢ μ D → U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            m' <- elabTerm ctx m mt
            let mv :: VElim HasMetas ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

                mv' = velim mv

            -- ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
            t' <- elabTerm ctx t $ evalTerm ctx.size (EmptyEnv :> velim (vann d VDsc) :> mv') muMotiveT

            -- ... ∈ M e
            let ev = evalElim ctx.size ctx.values e'
                ev' = velim ev
            return
                ( Ind e' m' t'
                , evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ)
                )

        _ -> elabError ctx "ind argument doesn't have type mu"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

elabElim' ctx (WSpl e) = do
    (e', et) <- elabElim ctx { cstage = succ ctx.cstage } e
    case force et of
        VCod a -> do
            return (Spl e', vsplCodArg ctx.size a)

        _ -> elabError ctx "splice argument doesn't have type Code"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

elabElim' ctx (WAnn t s) = do
    s' <- elabTerm ctx s VUni
    let sv = evalTerm ctx.size ctx.values s'
    t' <- elabTerm ctx t sv
    return (Ann t' s', sv)
elabElim' ctx (WLet x t s) = do
    (t', tt) <- elabElim ctx t
    (ctx', r) <- newRigid ctx tt
    let tv = evalElim ctx.size ctx.values t'
        tv' = EvalElim tv (SRgd r)
    (s', st) <- elabElim (bind' ctx' x tv' tt) s
    return (Let x t' s', st)
