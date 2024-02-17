-- | Type-checking.
--
-- We do some type-directed elaboration: desugaring list syntax,
-- but nothing which needs unification
module PoriTT.Check (
    CheckCtx,
    emptyCheckCtx,
    checkTerm,
    checkElim,
) where

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Conv
import PoriTT.Enum
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Lint
import PoriTT.Loc
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value
import PoriTT.Well

-------------------------------------------------------------------------------
-- Elaboration context
-------------------------------------------------------------------------------

-- | Elaboration context.
--
data CheckCtx ctx ctx' = CheckCtx
    { names   :: !(Env ctx Name)
    , names'  :: !(Env ctx' Name)
    , nscope  :: !NameScope
    , values  :: !(EvalEnv NoMetas ctx ctx')
    , types   :: !(Env ctx (VTerm NoMetas ctx'))
    , types'  :: !(Env ctx' (VTerm NoMetas ctx'))
    , stages  :: Env ctx Stage
    , cstage  :: Stage
    , size    :: !(Size ctx')
    , wk      :: Wk ctx' ctx               -- ^ weakening from target context to source context. This is possible, as target context is the same except the let bound values are missing.
    , loc     :: !(Loc)
    , doc     :: ![Doc]
    }

-- | Empty elaboration context.
--
-- Needs global 'NameScope' for pretty-printing.
--
emptyCheckCtx :: NameScope -> CheckCtx EmptyCtx EmptyCtx
emptyCheckCtx ns = CheckCtx
    { names  = EmptyEnv
    , names' = EmptyEnv
    , nscope = ns
    , values = EmptyEnv
    , types  = EmptyEnv
    , types' = EmptyEnv
    , stages = EmptyEnv
    , cstage = stage0
    , size   = SZ
    , wk     = IdWk
    , loc    = startLoc "<unknown>"
    , doc    = []
    }

toLintCtx :: CheckCtx ctx ctx' -> LintCtx ctx ctx'
toLintCtx ctx = LintCtx
    { values = ctx.values
    , types  = ctx.types
    , types' = ctx.types'
    , stages = ctx.stages
    , cstage = ctx.cstage
    , names  = ctx.names
    , names' = ctx.names'
    , nscope = ctx.nscope
    , size   = ctx.size
    , doc       = ctx.doc
    }

bind
    :: CheckCtx ctx ctx'
    -> Name                     -- ^ term name
    -> Name                     -- ^ name in types
    -> VTerm NoMetas ctx'       -- ^ type
    -> CheckCtx (S ctx) (S ctx')
bind (CheckCtx xs xs' ns v ts ts' ss cs s wk l pp) x x' a = CheckCtx
    { names   = xs :> x
    , names'  = xs' :> x'
    , nscope  = ns
    , values  = mapSink v :> t
    , types   = mapSink ts :> sink a
    , types'  = mapSink ts' :> sink a
    , stages  = ss :> cs
    , cstage  = cs
    , size    = SS s
    , wk      = KeepWk wk
    , loc     = l
    , doc     = pp
    }
  where
    t = evalZ s

bind'
    :: CheckCtx ctx ctx'
    -> Name                 -- ^ variable name
    -> EvalElim NoMetas ctx'   -- ^ value
    -> VTerm NoMetas ctx'   -- ^ type
    -> CheckCtx (S ctx) ctx'
bind' (CheckCtx xs xs' ns v ts ts' ss cs s wk l pp) x t a = CheckCtx
    { names   = xs :> x
    , names'  = xs'
    , nscope  = ns
    , values  = v :> t
    , types   = ts :> a
    , types'  = ts'
    , stages  = ss :> cs
    , cstage  = cs
    , size    = s
    , wk      = SkipWk wk
    , loc     = l
    , doc     = pp
    }

-------------------------------------------------------------------------------
-- Errors
-------------------------------------------------------------------------------

checkError :: CheckCtx ctx ctx' -> Doc -> [Doc] -> Either Doc a
checkError ctx msg extras = Left $ ppHanging
    (prettyLoc ctx.loc <> ":" <+> msg)
    [ ppBullet <+> ppAlign e
    | e <- extras ++ take 5 ctx.doc
    ]

notType :: CheckCtx ctx ctx' -> VTerm NoMetas ctx' -> Either Doc (Term NoMetas ctx)
notType ctx ty = checkError ctx "Checking against non-type"
    [ "not-type:" <+> prettyVTermCtx ctx ty
    ]

invalidTerm :: CheckCtx ctx ctx' -> Doc -> VTerm NoMetas ctx' -> Well (HasTerms NoMetas) ctx -> Either Doc (Term NoMetas ctx)
invalidTerm ctx cls ty t =  checkError ctx ("Checking against" <+> cls)
    [ "type:" <+> prettyVTermCtx ctx ty
    , "term:" <+> prettyWell ctx.nscope ctx.names 0 t
    ]

prettyVTermCtx :: CheckCtx ctx ctx' -> VTerm NoMetas ctx' -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names'

prettyNamesTypes :: Size ctx' -> NameScope -> Env ctx' Name -> Env ctx Name -> Env ctx (VTerm NoMetas ctx') -> [Doc]
prettyNamesTypes _ _  _   EmptyEnv  EmptyEnv  =  []
prettyNamesTypes s ns env (xs :> x) (ts :> t) =
    (prettyName x <+> ":" <+> t') :
    prettyNamesTypes s ns env xs ts
  where
    t' = case quoteTerm UnfoldElim s t of
        Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
        Right n  -> prettyTerm ns env 0 n

-------------------------------------------------------------------------------
-- Check & Infer wrappers
-------------------------------------------------------------------------------

-- | Check term ('Term') against a type (as 'VTerm').
checkTerm
    :: CheckCtx ctx ctx'               -- ^ Type checking context
    -> Well (HasTerms NoMetas) ctx     -- ^ Well scoped term
    -> VTerm NoMetas ctx'              -- ^ Expected type
    -> Either Doc (Term NoMetas ctx)   -- ^ Type checked term
checkTerm ctx t a = do
    let d = ppSep
            [ "When checking that"
            , prettyWell ctx.nscope ctx.names 0 t
            , "has type"
            , prettyVTermCtx ctx a
            ]
    checkTerm' ctx { doc = d : ctx.doc } t a

-- | Infer type of an elimination ('Elim').
checkElim
    :: CheckCtx ctx ctx'                                   -- ^ Type checking context
    -> Well (HasTerms NoMetas) ctx                         -- ^ Well scoped elimination
    -> Either Doc (Elim NoMetas ctx, VTerm NoMetas ctx')   -- ^ Type checked elimination and its type
checkElim ctx e = do
    let d = ppSep
            [ "When infering type of"
            , prettyWell ctx.nscope ctx.names 0 e
            ]
    checkElim' ctx { doc = d : ctx.doc } e

-------------------------------------------------------------------------------
-- Check helpers
-------------------------------------------------------------------------------

checkIcit :: CheckCtx ctx ctx' -> Icit -> Icit -> Either Doc ()
checkIcit ctx i j
    | i == j    = return ()
    | otherwise = checkError ctx "Icity mismatch"
        [ "expected:" <+> prettyIcit j
        , "actual:" <+> prettyIcit i
        ]

checkHole :: CheckCtx ctx ctx' -> Name -> VTerm NoMetas ctx' -> Either Doc (Term NoMetas ctx)
checkHole ctx n ty = checkError ctx ("Checking a hole" <+> prettyHole n) $
    [ "type:" <+> prettyVTermCtx ctx ty
    ] ++
    (prettyNamesTypes ctx.size ctx.nscope ctx.names' ctx.names ctx.types)

checkSkipped :: CheckCtx ctx ctx' -> VTerm NoMetas ctx' -> Either Doc (Term NoMetas ctx)
checkSkipped ctx ty = checkError ctx ("Skipped term") $
    [ "type:" <+> prettyVTermCtx ctx ty
    ] ++
    (prettyNamesTypes ctx.size ctx.nscope ctx.names' ctx.names ctx.types)

checkInfer :: CheckCtx ctx ctx' -> Well (HasTerms NoMetas) ctx -> VTerm NoMetas ctx' -> Either Doc (Term NoMetas ctx)
checkInfer ctx e            a = do
    (e', et) <- checkElim ctx e
    -- traceM $ "CONV: " ++ show (ctx.names', e, et, a)
    case convTerm (mkConvCtx ctx.size ctx.names' ctx.types' ctx.nscope) VUni a et of
        Right () -> pure (Emb e')
        Left err -> checkError ctx "Couldn't match types"
            [ "expected:" <+> prettyVTermCtx ctx a
            , "actual:" <+> prettyVTermCtx ctx et
            , err
            ]

checkLabel :: CheckCtx ctx ctx' -> Label -> [Label] -> Either Doc EnumIdx
checkLabel ctx l0 ls0 = go 0 ls0 where
    go :: Int -> [Label] -> Either Doc EnumIdx
    go !_ [] = checkError ctx ("label" <+> prettyLabel l0 <+> "is not in the set" <+> prettyVTermCtx ctx (VFin ls0)) []
    go !i (l:ls)
        | l == l0   = return (EnumIdx i)
        | otherwise = go (i + 1) ls

checkEnumIdx :: CheckCtx ctx ctx' -> EnumIdx -> [Label] -> Either Doc EnumIdx
checkEnumIdx ctx i@(EnumIdx i') ls0
    | i' < length ls0 = return i
    | otherwise = checkError ctx ("enum index " <+> prettyEnumIdx i <+> "is out of bounds of" <+> prettyVTermCtx ctx (VFin ls0)) []

-- TODO: Better name for this.
foo :: CheckCtx ctx ctx' -> [Label] -> [Either Label EnumIdx := a] -> Either Doc (EnumList a)
foo ctx ls0 m0 = go 0 [] m0 ls0 where
    go _ tgt src []
        | null src   = return $ makeEnumList $ reverse tgt
        | otherwise = checkError ctx "switch map contains extra keys"
            [ ppStr (show (map fst src))
            ]

    go i' tgt src (l:ls)
        | Just (x, src') <- lookupRemoving (Left l) src
        = go (i' + 1) (x : tgt) src' ls

        | Just (x, src') <- lookupRemoving (Right i) src
        = go (i' + 1) (x : tgt) src' ls

        | otherwise
        = checkError ctx "switch map doesn't contain a key"
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

checkTerm'
    :: CheckCtx ctx ctx'                -- ^ Type checking context
    -> Well (HasTerms NoMetas) ctx      -- ^ Well scoped term
    -> VTerm NoMetas ctx'               -- ^ Expected type
    -> Either Doc (Term NoMetas ctx)    -- ^ Type checked term
checkTerm' ctx (WLoc l t) ty = checkTerm' ctx { loc = l } t ty
checkTerm' ctx (WHol n)   ty = checkHole ctx n ty
checkTerm' ctx WSkp       ty = checkSkipped ctx ty
checkTerm' ctx e@WVar {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WGbl {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WApp {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WSel {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WSwh {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WDeI {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WInd {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WSpl {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WAnn {}  ty = checkInfer ctx e ty
checkTerm' ctx e@WLet {}  ty = checkInfer ctx e ty
checkTerm' ctx (WTcT t)   ty = do
    lintTerm (toLintCtx ctx) t ty
    return t
checkTerm' ctx t          ty = checkTerm'' ctx ty t

checkTerm''
    :: CheckCtx ctx ctx'               -- ^ Type checking context
    -> VTerm NoMetas ctx'              -- ^ Expected type
    -> Well (HasTerms NoMetas) ctx     -- ^ Well scoped term
    -> Either Doc (Term NoMetas ctx)   -- ^ Type checked term
checkTerm'' ctx (VEmb (VErr msg)) _t = do
    checkError ctx "Type evaluation error"
        [ ppStr (show msg)
        ]

-- types
checkTerm'' _ctx VUni WUni = return Uni
checkTerm'' _ctx VUni WOne = return One
checkTerm'' _ctx VUni WDsc = return Dsc
checkTerm'' _ctx VUni (WFin ls) = return (Fin ls)
checkTerm''  ctx VUni (WPie x i a b) = do
    a' <- checkTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- checkTerm (bind ctx x x av) b VUni
    return (Pie x i a' b')
checkTerm'' ctx VUni (WSgm x i a b) = do
    a' <- checkTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- checkTerm (bind ctx x x av) b VUni
    return (Sgm x i a' b')
checkTerm'' ctx VUni (WMuu t) = do
    t' <- checkTerm ctx t VDsc
    return (Muu t')
checkTerm'' ctx VUni (WCod t) = do
    t' <- checkTerm ctx t vcodUni
    return (Cod t')
checkTerm'' ctx ty@VUni t = do
    invalidTerm ctx "U" ty t

-- functions
checkTerm'' ctx (VPie y i a b) (WLam x j t) = do
    checkIcit ctx i j
    let ctx' = bind ctx x y a
    t' <- checkTerm ctx' t (runZ ctx.size b)
    return (Lam x i t')
checkTerm'' ctx (VPie x Ecit (force -> VFin ls) b) (WLst ts) = do
    --
    let x' = nonAnonName x
    let ty = VPie x' Ecit (VFin ls) b
    b' <- case quoteTerm UnfoldNone ctx.size (VLam x' Ecit b) of
        Left err -> checkError ctx "Evaluation error"
            [ ppStr (show err)
            ]
        Right b' -> return b'

    let b'' = weaken ctx.wk b'
    let ts' = ifoldr (\i t acc -> (Right (EnumIdx i) := weaken wk1 t) : acc) [] ts
    checkTerm ctx (WLam x' Ecit $ WSwh (WVar IZ) (weaken wk1 (WTcT b'')) ts') ty
checkTerm'' ctx ty@(VPie _ _ _ _) t =
    invalidTerm ctx "Pi-type" ty t

-- pairs
checkTerm'' ctx (VSgm _ j a b) (WMul i t s) = do
    checkIcit ctx i j
    t' <- checkTerm' ctx t a
    let tv = evalTerm ctx.size ctx.values t'
    s' <- checkTerm ctx s (run ctx.size b (vann tv a))
    return (Mul i t' s')
checkTerm'' ctx (VSgm x Ecit a b) (WLst ts0) = do
    --
    -- ⊩ Σ (x : A) × B ∋ t , [s...] ▹ r
    -- --------------------------------
    -- ⊩ Σ (x : A) × B ∋ [ t s...] ▹ r
    --
    case ts0 of
        [] -> checkError ctx
            "Null list expression checked against sigma type"
            []
        t:ts -> do
            checkTerm ctx (WMul Ecit t (WLst ts)) (VSgm x Ecit a b)
checkTerm'' ctx ty@(VSgm _ _ _ _) t =
    invalidTerm ctx "Sigma-type" ty t

-- unit
checkTerm'' _ctx VOne WTht =
    return Tht
checkTerm'' ctx VOne (WLst ts) = do
    --
    -- ------------------
    -- ⊩ Unit ∋ [] ▹ tt
    --
    when (not (null ts)) $ checkError ctx
        "Non-null list expression checked against enum type"
        []
    return Tht
checkTerm'' ctx ty@VOne t =
    invalidTerm ctx "Unit" ty t

-- descriptions
checkTerm'' _ctx VDsc WDe1 =
    return De1
checkTerm'' ctx VDsc (WDeS t s) = do
    t' <- checkTerm ctx t VUni
    s' <- checkTerm ctx s (VPie "_" Ecit (evalTerm ctx.size ctx.values t') (Closure EmptyEnv Dsc))
    return (DeS t' s')
checkTerm'' ctx VDsc (WDeX t) = do
    t' <- checkTerm ctx t VDsc
    return (DeX t')
checkTerm'' ctx ty@VDsc t =
    invalidTerm ctx "Description" ty t

-- fixed points
checkTerm'' ctx ty@(VMuu d) (WCon t) = do
    t' <- checkTerm ctx t $ vemb $ vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, ty]
    return (Con t')
checkTerm'' ctx (VMuu (force -> VDeS (force -> VFin ls) d)) (WLbl l ts) = do
    --
    -- ⊩ #E ∋ :c ▹ n
    -- ⊩ evalDesc ((D : #E → Desc) n) (μ (`Σ E# D)) ∋ [t...] ▹ t'
    -- ------------------------------------------------------------
    -- ⊩ μ (`Σ #E D) ∋ :c t... ▹ con (n , t')
    --
    i' <- checkLabel ctx l ls
    let d' = vann d (VPie "_" Ecit (VFin ls) (Closure EmptyEnv Dsc))
    t' <- checkTerm ctx (WLst ts) $ vemb $ vapps ctx.size (vgbl ctx.size evalDescGlobal)
        [ vemb (vapp ctx.size Ecit d' (VEIx i'))
        , VMuu (VDeS (VFin ls) d)
        ]

    return $ Con (Mul Ecit (EIx i') t')

checkTerm'' ctx ty@(VMuu _) t =
    invalidTerm ctx "Mu-type" ty t

-- finite enumerations
checkTerm'' ctx (VFin ls) (WLbl l ts) = do
    unless (null ts) $ checkError ctx
        ("label" <+> prettyLabel l <+> "is applied to arguments but checked against finite set type")
        []
    i' <- checkLabel ctx l ls
    return (EIx i')
checkTerm'' ctx (VFin ls) (WEIx i ts) = do
    unless (null ts) $ checkError ctx
        ("enum index " <+> prettyEnumIdx i <+> "is applied to arguments but checked against finite set type")
        []
    i' <- checkEnumIdx ctx i ls
    return (EIx i')
checkTerm'' ctx ty@(VFin _) t =
    invalidTerm ctx "finite enumeration" ty t

-- code
checkTerm'' ctx (VCod a) (WQuo t) = do
    t' <- checkTerm ctx { cstage = pred ctx.cstage } t (vsplCodArg ctx.size a)
    return (Quo t')
checkTerm'' ctx ty@(VCod _) t =
    invalidTerm ctx "Code" ty t

-- not types
checkTerm'' ctx ty@VLam {} _ = notType ctx ty
checkTerm'' ctx ty@VDe1 {} _ = notType ctx ty
checkTerm'' ctx ty@VDeS {} _ = notType ctx ty
checkTerm'' ctx ty@VDeX {} _ = notType ctx ty
checkTerm'' ctx ty@VCon {} _ = notType ctx ty
checkTerm'' ctx ty@VMul {} _ = notType ctx ty
checkTerm'' ctx ty@VEIx {} _ = notType ctx ty
checkTerm'' ctx ty@VQuo {} _ = notType ctx ty
checkTerm'' ctx ty@VTht {} _ = notType ctx ty

-- emb ann should be reduced, but we don't enforce that.
checkTerm'' ctx (VEmb (VAnn ty _))  t = checkTerm'' ctx ty t

-- force
checkTerm'' ctx (VEmb (VGbl _ _ v)) t = checkTerm'' ctx (vemb v) t

checkTerm'' ctx (VEmb ty@(VRgd _ _)) _ =
    checkError ctx "Cannot check against neutral-type"
        [ "type:" <+> prettyVTermCtx ctx (VEmb ty)
        ]

-------------------------------------------------------------------------------
-- Check Elim
-------------------------------------------------------------------------------

checkElim' :: forall ctx ctx'. CheckCtx ctx ctx' -> Well (HasTerms NoMetas) ctx -> Either Doc (Elim NoMetas ctx, VTerm NoMetas ctx')
checkElim' ctx (WLoc l r)
    = checkElim' ctx { loc = l } r
checkElim' ctx (WVar i) = do
    let s = lookupEnv i ctx.stages
    when (s /= ctx.cstage) $ do
        checkError ctx "Variable used at different stage"
            [ "variable:" <+> prettyName (lookupEnv i ctx.names)
            , "expected:" <+> prettyStage ctx.cstage
            , "actual:  " <+> prettyStage s
            ]

    pure (Var i, lookupEnv i ctx.types)
checkElim' ctx (WGbl g) =
    pure (Gbl g, sinkSize ctx.size g.typ)
checkElim' ctx (WHol n) =
    checkError ctx
    ("Cannot infer type of a hole" <> prettyHole n)
    []
checkElim' ctx WSkp =
    checkError ctx
    ("Cannot infer type of skipped term")
    []
checkElim' ctx (WLam _ _ _) =
    checkError ctx
    "Cannot infer type of a lambda abstraction"
    []
checkElim' ctx (WMul _ _ _) =
    checkError ctx
    "Cannot infer type of a pair constructor"
    []
checkElim' ctx (WCon _) =
    checkError ctx
    "Cannot infer type of a con constructor"
    []
checkElim' ctx (WLbl _ _) =
    checkError ctx
    "Cannot infer type of a label"
    []
checkElim' ctx (WEIx _ _) =
    checkError ctx
    "Cannot infer type of an enum index"
    []
checkElim' ctx (WQuo _) =
    checkError ctx
    "Cannot infer type of a quote"
    []
checkElim' ctx (WLst _) =
    checkError ctx
    "Cannot infer type of a list expression"
    []
checkElim' ctx  (WTcT _) =
    checkError ctx
    "Cannot infer type of a embedded type-checker term"
    []
checkElim' ctx (WPie x i a b) = do
    a' <- checkTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- checkTerm (bind ctx x x av) b VUni
    return (Ann (Pie x i a' b') Uni, VUni)
checkElim' ctx (WSgm x i a b) = do
    a' <- checkTerm ctx a VUni
    let av = evalTerm ctx.size ctx.values a'
    b' <- checkTerm (bind ctx x x av) b VUni
    return (Ann (Sgm x i a' b') Uni, VUni)
checkElim' _   (WFin ls) =
    return (Ann (Fin ls) Uni, VUni)
checkElim' _   WUni =
    return (Ann Uni Uni, VUni)
checkElim' _   WOne =
    return (Ann One Uni, VUni)
checkElim' _   WTht =
    return (Ann Tht One, VOne)
checkElim' _   WDsc =
    return (Ann Dsc Uni, VUni)
checkElim' _   WDe1 =
    return (Ann De1 Dsc, VDsc)
checkElim' ctx (WDeX t) = do
    t' <- checkTerm ctx t VDsc
    return (Ann (DeX t') Dsc, VDsc)
checkElim' ctx (WDeS t s) = do
    t' <- checkTerm ctx t VUni
    let tv = evalTerm ctx.size ctx.values t'
    s' <- checkTerm ctx s (VPie "_" Ecit tv (Closure EmptyEnv Dsc))
    return (Ann (DeS t' s') Dsc, VDsc)
checkElim' ctx (WMuu t) = do
    t' <- checkTerm ctx t VDsc
    return (Ann (Muu t') Uni, VUni)
checkElim' ctx (WCod a) = do
    a' <- checkTerm ctx a vcodUni
    return (Ann (Cod a') Uni, VUni)
checkElim' ctx (WApp i f t) = do
    (f', ft) <- checkElim ctx f
    case force ft of
        VPie _ j a b -> do
            checkIcit ctx j i
            t' <- checkTerm ctx t a
            let tv = evalTerm ctx.size ctx.values t'
            return (App i f' t', run ctx.size b (vann tv a))
        _ -> checkError ctx "Function application head does not have a pi-type"
            [ "actual:" <+> prettyVTermCtx ctx ft
            ]
checkElim' ctx (WSel e s) = do
    (e', et) <- checkElim ctx e
    case force et of
        VSgm _ _i a b
            | s == "fst" -> return (Sel e' s, a)
            | s == "snd" -> return (Sel e' s, run ctx.size b (evalElim ctx.size ctx.values (Sel e' "fst")))
            | otherwise  -> checkError ctx ("Sigma type doesn't have field" <+> prettySelector s) []

        -- TODO: pie with a ~ WFin
        _ -> checkError ctx "Selector application head does not have a selectable type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

checkElim' ctx (WSwh e m ts) = do
    (e', et) <- checkElim ctx e
    case force et of
        VFin ls -> do
            ts0 <- foo ctx ls ts

            -- {:ls...} -> U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            m' <- checkTerm ctx m mt
            let mv :: VElim NoMetas ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

                mv' = velim mv

            -- in { :l -> t }
            -- M :l ∋ t
            ts' <- ifor ts0 $ \i t -> do
                checkTerm ctx t $ evalTerm ctx.size (EmptyEnv :> mv') (var IZ @@ EIx i)

            let ev = evalElim ctx.size ctx.values e'
                ev' = velim ev
            return (Swh e' m' ts', evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ))

        _ -> checkError ctx "Switch case scrutinee doesn't have finite set type"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

checkElim' ctx (WDeI e m c1 cS cX) = do
    -- ⊢ e ∈ Desc
    (e', et) <- checkElim ctx e
    case force et of
        VDsc -> do
            -- ⊢ Desc → U ∋ M
            let mt = evalTerm ctx.size EmptyEnv descIndMotive
            m' <- checkTerm ctx m mt
            let mv :: VElim NoMetas ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

                mv' = velim mv

            -- ⊢ M `1 ∋ c1
            c1' <- checkTerm ctx c1 $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotive1

            -- ⊢ Π (S : U) (D : S → Desc) → (Π (s : S) → M (D s)) → M (`S S D) ∋ cS
            cS' <- checkTerm ctx cS $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotiveS

            -- ⊢ Π (D : Desc) → M D → M (`X D) ∋ cX
            cX' <- checkTerm ctx cX $ evalTerm ctx.size (EmptyEnv :> mv') descIndMotiveX

            -- ∈ M e
            let ev = evalElim ctx.size ctx.values e'
                ev' = velim ev

            return
              ( DeI e' m' c1' cS' cX'
              , evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ)
              )

        _ -> checkError ctx "Desc induction scrutinee doesn't have type Desc"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

checkElim' ctx (WInd e m t) = do
    -- ⊢ e ∈ μ D
    (e', et) <- checkElim ctx e
    case force et of
        VMuu d -> do
            -- ⊢ μ D → U ∋ M
            let mt = VPie "_" Ecit et (Closure EmptyEnv Uni)
            m' <- checkTerm ctx m mt
            let mv :: VElim NoMetas ctx'
                mv = vann (evalTerm ctx.size ctx.values m') mt

                mv' = velim mv

            -- ⊢ Π (d : evalDesc D (μ D)) → All D (μ D) M d → M (con d) ∋ t
            t' <- checkTerm ctx t $ evalTerm ctx.size (EmptyEnv :> velim (vann d VDsc) :> mv') muMotiveT

            -- ... ∈ M e
            let ev = evalElim ctx.size ctx.values e'
                ev' = velim ev
            return
                ( Ind e' m' t'
                , evalTerm ctx.size (ctx.values :> mv' :> ev') (var I1 @@ var IZ)
                )

        _ -> checkError ctx "ind argument doesn't have type mu"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

checkElim' ctx (WSpl e) = do
    (e', et) <- checkElim ctx { cstage = succ ctx.cstage } e
    case force et of
        VCod a -> do
            return (Spl e', vsplCodArg ctx.size a)

        _ -> checkError ctx "splice argument doesn't have type Code"
            [ "actual:" <+> prettyVTermCtx ctx et
            ]

checkElim' ctx (WAnn t s) = do
    s' <- checkTerm ctx s VUni
    let sv = evalTerm ctx.size ctx.values s'
    t' <- checkTerm ctx t sv
    return (Ann t' s', sv)
checkElim' ctx (WLet x t s) = do
    (t', tt) <- checkElim ctx t
    let tv = evalElim ctx.size ctx.values t'
        tv' = velim tv -- TODO
    (s', st) <- checkElim (bind' ctx x tv' tt) s
    return (Let x t' s', st)
