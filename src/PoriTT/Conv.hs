-- | Beta-eta conversion checking
--
-- We can check for beta-eta equality in semantic domain, i.e. on 'VTerm's and 'VElim's.
module PoriTT.Conv (
    convTerm,
    convElim,
    ConvCtx,
    mkConvCtx,
) where

import PoriTT.Base
import PoriTT.Builtins
import PoriTT.Enum
import PoriTT.Eval
import PoriTT.ExceptState
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Rigid
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

-- | Conversion context.
data ConvCtx pass ctx = ConvCtx
    { size   :: Size ctx
    , names  :: Env ctx Name
    , types  :: Env ctx (VTerm pass ctx)
    , nscope :: NameScope
    , rigids :: RigidMap ctx (VTerm pass ctx) -- We could add names here to have nicer rigid printing
    }

bind :: Name -> VTerm pass ctx -> ConvCtx pass ctx -> ConvCtx pass (S ctx)
bind x t (ConvCtx s xs ts gs rs) = ConvCtx (SS s) (xs :> x) (mapSink ts :> sink t) gs (rigidMapSink (mapSink rs))

type ConvM = ExceptState Doc RigidGen

newRigid :: ConvCtx pass ctx -> VTerm pass ctx -> ConvM (ConvCtx pass ctx, RigidVar ctx)
newRigid ctx ty = do
    r <- newRigidVar
    return (ctx { rigids = insertRigidMap r ty ctx.rigids }, r)

-- | Create conversion context.
--
-- Requires
--
-- * context size
--
-- * names of the variables in the cotnext (for pretty printing)
--
-- * types of things in context
--
-- * and a global 'NameScope' (for pretty-printing)
--
mkConvCtx :: Size ctx -> Env ctx Name -> Env ctx (VTerm pass ctx) -> NameScope -> RigidMap ctx (VTerm pass ctx) -> ConvCtx pass ctx
mkConvCtx = ConvCtx

prettyVTermCtx :: ConvCtx pass ctx -> VTerm pass ctx -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names

prettySTermCtx :: Natural -> ConvCtx pass ctx -> STerm pass ctx -> Doc
prettySTermCtx l ctx = prettySTerm l ctx.size ctx.nscope ctx.names

prettySElimCtx :: Natural -> ConvCtx pass ctx -> SElim pass ctx -> Doc
prettySElimCtx l ctx = prettySElim l ctx.size ctx.nscope ctx.names

lookupLvl :: ConvCtx pass ctx -> Lvl ctx -> Name
lookupLvl ctx l = lookupEnv (lvlToIdx ctx.size l) ctx.names

mismatch :: Doc -> Doc -> Doc -> ConvM a
mismatch t x y = throwError $ t <+> "mismatch:" <+> x <+> "/=" <+> y

notConvertible :: ConvCtx pass ctx -> VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx -> ConvM a
notConvertible ctx ty x y = throwError $ ppSep
    [ "not convertible:"
    , prettyVTermCtx ctx ty <+> ":"
    , prettyVTermCtx ctx x <+> "/="
    , prettyVTermCtx ctx y
    ]

notConvertibleST :: Natural -> ConvCtx pass ctx -> VTerm pass ctx -> STerm pass ctx -> STerm pass ctx -> ConvM a
notConvertibleST l ctx ty x y = throwError $ ppSep
    [ "not convertible (at level" <+> ppStr (show l) <> "):"
    , prettyVTermCtx ctx ty <+> ":"
    , prettySTermCtx l ctx x <+> "/="
    , prettySTermCtx l ctx y
    ]

notConvertibleSE :: Natural -> ConvCtx pass ctx -> SElim pass ctx -> SElim pass ctx -> ConvM a
notConvertibleSE l ctx x y = throwError $ ppSep
    [ "not convertible (at level" <+> ppStr (show l) <> "):"
    , prettySElimCtx l ctx x <+> "/="
    , prettySElimCtx l ctx y
    -- , ppStr $ show x
    -- , ppStr $ show y
    ]

notType :: ConvCtx pass ctx -> VTerm pass ctx -> ConvM a
notType ctx ty = throwError $ ppSep
    [ "CONV PANIC: NOT A TYPE"
    , prettyVTermCtx ctx ty
    ]

-- | Beta-eta conversion checking of terms.
--
-- The last argument is a common type of the terms.
-- The conversion checking is (somewhat) type-directed, we need
-- types for do eta-expansion.
--
convTerm :: ConvCtx pass ctx -> VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx -> ConvM ()
convTerm ctx ty x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    convTerm' ctx ty x y

-- | Beta-eta conversion checking of eliminations.
convElim :: ConvCtx pass ctx -> VElim pass ctx -> VElim pass ctx -> ConvM (VTerm pass ctx)
convElim ctx x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    convElim' ctx x y

-- | Beta-eta conversion checking of eliminations.
convNeut :: ConvCtx pass ctx -> VNeut pass ctx -> VNeut pass ctx -> ConvM (VTerm pass ctx)
convNeut ctx x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    convNeut' ctx x y

-------------------------------------------------------------------------------
-- Workers
-------------------------------------------------------------------------------

convIcit :: ConvCtx pass ctx -> Icit -> Icit -> ConvM ()
convIcit _ctx i j
    | i == j    = return ()
    | otherwise = mismatch "icity" (prettyIcit i) (prettyIcit j)

convTerm' :: ConvCtx pass ctx -> VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx -> ConvM ()
convTerm' ctx (VEmb (VGbl _ _ t)) x y  = convTerm ctx (vemb t) x y
convTerm' ctx ty (VEmb (VGbl _ _ x)) y = convTerm ctx ty (vemb x) y
convTerm' ctx ty x (VEmb (VGbl _ _ y)) = convTerm ctx ty x (vemb y)

convTerm' ctx (VEmb (VAnn t _)) x y = convTerm' ctx t x y

-- ⊢ U ∋ t ≡ s
convTerm' _   VUni VUni             VUni           = pure ()
convTerm' _   VUni VDsc             VDsc           = pure ()
convTerm' _   VUni VOne             VOne           = pure ()
convTerm' ctx VUni (VPie x i a1 b1) (VPie _ j a2 b2) = convIcit ctx i j >> convTerm ctx VUni a1 a2 >> convTerm (bind x a1 ctx) VUni (runZ ctx.size b1) (runZ ctx.size b2)
convTerm' ctx VUni (VSgm x i a1 b1) (VSgm _ j a2 b2) = convIcit ctx i j >> convTerm ctx VUni a1 a2 >> convTerm (bind x a1 ctx) VUni (runZ ctx.size b1) (runZ ctx.size b2)
convTerm' ctx VUni (VMuu x)         (VMuu y)       = convTerm ctx VDsc x y
convTerm' ctx VUni (VEmb (VRgd x sp1)) (VEmb (VRgd y sp2))   = void $ convNeutral ctx x sp1 y sp2
convTerm' _   VUni (VFin ls1)       (VFin ls2)     = if ls1 == ls2 then pure () else mismatch "finite set" (prettyLabels ls1) (prettyLabels ls2)
convTerm' ctx VUni (VCod x)         (VCod y)       = convTerm ctx vcodUni x y
convTerm' ctx VUni x                y              = notConvertible ctx VUni x y

-- ⊢ Π (x : A) → B ∋ t ≡ s
convTerm' ctx (VPie _ _ a b) (VLam x i b1)  (VLam _ j b2) = convIcit ctx i j >> convTerm (bind x a ctx) (runZ ctx.size b) (runZ ctx.size b1)  (runZ ctx.size b2)
convTerm' ctx (VPie _ _ a b) (VLam x i b1)  (VEmb u)      = convTerm (bind x a ctx) (runZ ctx.size b) (runZ ctx.size b1)  (etaLam ctx.size i u)
convTerm' ctx (VPie _ _ a b) (VEmb t)       (VLam x i b2)   = convTerm (bind x a ctx) (runZ ctx.size b) (etaLam ctx.size i t) (runZ ctx.size b2)
convTerm' ctx (VPie x i a b) (VEmb t)       (VEmb u)        = convTerm (bind x a ctx) (runZ ctx.size b) (etaLam ctx.size i t) (etaLam ctx.size i u)
-- convTerm' ctx (VPie _ _ _) (VRgd x sp1)   (VRgd y sp2)   = convNeutral ctx x sp1 y sp2
convTerm' ctx (VPie z i a b) x              y               = notConvertible ctx (VPie z i a b) x y

-- ⊢ Σ (z : A) × B ∋ t ≡ s
convTerm' ctx (VSgm _ _ a b) (VMul i x1 y1) (VMul j x2 y2) = convIcit ctx i j >> convTerm ctx a x1 x2 >> convTerm ctx (run ctx.size b (vann x1 a)) y1 y2
convTerm' ctx (VSgm _ _ a b) (VMul _ x y)   (VEmb q)       = convTerm ctx a x (vemb (vsel ctx.size q "fst")) >> convTerm ctx (run ctx.size b (vann x a)) y (vemb (vsel ctx.size q "snd"))
convTerm' ctx (VSgm _ _ a b) (VEmb p)       (VMul _ x y)   = convTerm ctx a (vemb (vsel ctx.size p "fst")) x >> convTerm ctx (run ctx.size b (vann x a)) (vemb (vsel ctx.size p "snd")) y
convTerm' ctx (VSgm _ _ a b) (VEmb p)       (VEmb q)       = do
    let p1 = vsel ctx.size p "fst"
    convTerm ctx a                   (vemb p1)                      (vemb (vsel ctx.size q "fst"))
    convTerm ctx (run ctx.size b p1) (vemb (vsel ctx.size p "snd")) (vemb (vsel ctx.size q "snd"))
-- convTerm' ctx (VSgm _ _ _) (VRgd x sp1)   (VRgd y sp2)   = convNeutral ctx x sp1 y sp2
convTerm' ctx (VSgm z i a b) x              y              = notConvertible ctx (VSgm z i a b) x y

-- ⊢ Unit ∋ t ≡ s
convTerm' _   VOne      _            _            = pure ()

-- ⊢ {:a ... :z} ∋ t ≡ s
convTerm' _   (VFin _)  (VEIx i1)    (VEIx i2)    = if i1 == i2 then pure () else mismatch "enum idx" (prettyEnumIdx i1) (prettyEnumIdx i2)
convTerm' _   (VFin ls) _            _
    -- eta expansion singletons: treat all elements equally
    | length ls == 1                              = pure ()
convTerm' ctx (VFin _)  (VEmb x)     (VEmb y)     = void (convElim ctx x y)
convTerm' ctx (VFin ls) x            y            = notConvertible ctx (VFin ls) x y

-- ⊢ Desc ∋ t ≡ s
convTerm' _   VDsc VDe1           VDe1           = pure ()
convTerm' ctx VDsc (VDeS t1 s1)   (VDeS t2 s2)   = do
    convTerm ctx VUni t1 t2
    convTerm ctx (VPie "S" Ecit t1 (Closure EmptyEnv Dsc)) s1 s2
convTerm' ctx VDsc (VDeX t1)      (VDeX t2)      = do
    convTerm ctx VDsc t1 t2
convTerm' ctx VDsc (VEmb x)       (VEmb y)       = void (convElim ctx x y)
convTerm' ctx VDsc x              y              = notConvertible ctx VDsc x y

-- ⊢ μ d ∋ t ≡ s
convTerm' ctx (VMuu d) (VCon x)       (VCon y)     = do
    let xty = vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, VMuu d]
    convTerm ctx (vemb xty) x y
convTerm' ctx (VMuu _) (VEmb x)       (VEmb y)     = void (convElim ctx x y)
convTerm' ctx (VMuu d) x              y            = notConvertible ctx (VMuu d) x y

-- ⊢ Code a ∋ t ≡ s
convTerm' ctx (VCod a) (VQuo x _)     (VQuo y _)   = do
    convSTerm NZ ctx (vsplCodArg ctx.size a) x y
convTerm' ctx (VCod _) (VEmb x)       (VEmb y)     = void (convElim ctx x y)
convTerm' ctx (VCod a) x              y            = notConvertible ctx (VCod a) x y

-- Only neutral terms can be convertible under neutral type
convTerm' ctx (VEmb VRgd {})     (VEmb x) (VEmb y) = void (convElim ctx x y)
convTerm' ctx (VEmb (VRgd h sp)) x y = notConvertible ctx (VEmb (VRgd h sp)) x y

convTerm' _   (VEmb (VErr msg)) _ _ = throwError $ ppStr $ show msg
convTerm' ctx ty@(VEmb (VFlx _ _)) _ _ = notType ctx ty

-- value constructors cannot be types
convTerm' ctx ty@VLam {} _ _ = notType ctx ty
convTerm' ctx ty@VDe1 {} _ _ = notType ctx ty
convTerm' ctx ty@VDeS {} _ _ = notType ctx ty
convTerm' ctx ty@VDeX {} _ _ = notType ctx ty
convTerm' ctx ty@VCon {} _ _ = notType ctx ty
convTerm' ctx ty@VMul {} _ _ = notType ctx ty
convTerm' ctx ty@VEIx {} _ _ = notType ctx ty
convTerm' ctx ty@VQuo {} _ _ = notType ctx ty
convTerm' ctx ty@VTht {} _ _ = notType ctx ty

convElim' :: ConvCtx pass ctx -> VElim pass ctx -> VElim pass ctx -> ConvM (VTerm pass ctx)
-- Globals
convElim' env (VGbl g1 VNil _) (VGbl g2 VNil _)
    | g1.name == g2.name   = pure (coeNoMetasVTerm (sinkSize env.size g1.typ))
-- otherwise we check the values
convElim' ctx (VGbl _ _ t)   u             = convElim ctx t u
convElim' ctx t              (VGbl _ _ u)  = convElim ctx t u
convElim' ctx (VRgd h1 sp1)  (VRgd h2 sp2) = convNeutral ctx h1 sp1 h2 sp2
convElim' ctx (VAnn t ty)    e             = convTerm ctx ty t (vemb e) >> return ty
convElim' ctx e              (VAnn t ty)   = convTerm ctx ty (vemb e) t >> return ty
convElim' _   (VErr msg)     _             = throwError $ ppStr $ show msg
convElim' _   _              (VErr msg)    = throwError $ ppStr $ show msg
convElim' _   (VFlx _ _)     _             = throwError "flex"
convElim' _   _              (VFlx _ _)    = throwError "flex"

convNeut' :: ConvCtx pass ctx -> VNeut pass ctx -> VNeut pass ctx -> ConvM (VTerm pass ctx)
-- Globals
convNeut' ctx (VNRgd h1 sp1)  (VNRgd h2 sp2) = convNeutral ctx h1 sp1 h2 sp2
convNeut' _   (VNErr msg)     _             = throwError $ ppStr $ show msg
convNeut' _   _              (VNErr msg)    = throwError $ ppStr $ show msg
convNeut' _   (VNFlx _ _)     _             = throwError "flex"
convNeut' _   _              (VNFlx _ _)    = throwError "flex"

-- Eta expand value of function type.
etaLam :: Size ctx -> Icit -> VElim pass ctx -> VTerm pass (S ctx)
etaLam s i f = vemb (vapp (SS s) i (sink f) (vemb (valZ s)))

-------------------------------------------------------------------------------
-- Rigid
-------------------------------------------------------------------------------

convNeutral :: ConvCtx pass ctx -> Lvl ctx -> Spine pass ctx -> Lvl ctx -> Spine pass ctx -> ConvM (VTerm pass ctx)
convNeutral ctx x sp1 y sp2
    | x == y    = do
        -- traceM "convNeutral"
        -- traceM $ show $ prettyVTermCtx ctx (VRgd x sp1)
        -- traceM $ show $ prettyVTermCtx ctx (VRgd y sp2)
        -- traceM $ show $ prettyVTermCtx ctx headTy
        convSpine ctx x sp1 sp2
    | otherwise = mismatch "spine head" (prettyName (lookupLvl ctx x)) (prettyName (lookupLvl ctx y))

convSpine :: forall ctx pass. ConvCtx pass ctx -> Lvl ctx -> Spine pass ctx -> Spine pass ctx -> ConvM (VTerm pass ctx)
convSpine ctx headLvl sp1' sp2' = do
    let len1 = spineLength sp1'
        len2 = spineLength sp2'

    unless (len1 == len2) $
        mismatch "spine length" (ppInt (spineLength sp1')) (ppInt (spineLength sp2'))

    snd <$> go sp1' sp2'

  where
    headTy :: VTerm pass ctx
    headTy = lookupEnv (lvlToIdx ctx.size headLvl) ctx.types

    go :: Spine pass ctx -> Spine pass ctx -> ConvM (VElim pass ctx, VTerm pass ctx)
    go VNil VNil = pure (VRgd headLvl VNil, headTy)
    go (VApp sp1 i x) (VApp sp2 j y) = do
        (h, ty) <- go sp1 sp2
        case force ty of
            VPie _ _ a b -> do
                convIcit ctx i j
                convTerm ctx a x y
                return (vapp ctx.size i h x, run ctx.size b (vann x a))

            _ -> TODO

    go (VSel sp1 x) (VSel sp2 y) = do
        (h, ty) <- go sp1 sp2
        unless (x == y ) $ mismatch "selector" (prettySelector x) (prettySelector y)
        case force ty of
            VSgm _ _ a b -> case x of
                "fst" -> return (vsel ctx.size h x, a)
                "snd" -> return (vsel ctx.size h x, run ctx.size b (vsel ctx.size h "fst"))
                _     -> throwError $ "conv panic: sigma with" <+> prettySelector x

            _ -> TODO
        
    go (VSwh sp1 m1 xs) (VSwh sp2 m2 ys) = do
        (h, ty) <- go sp1 sp2
        unless (length xs == length ys) $ mismatch "switch case arity" (ppInt (length xs)) (ppInt (length ys))
        case force ty of
            VFin ls -> do
                convTerm ctx (VPie "_" Ecit (VFin ls) (Closure EmptyEnv Uni)) m1 m2
                let m :: VElim pass ctx
                    m = vann m1 $ varr (VFin ls) Uni

                ifor_ ls $ \i' l -> do
                    let i = EnumIdx i'
                    x <- maybe (throwError $ "missing case in throwError"  <+> prettyLabel l) return $ lookupEnumList i xs
                    y <- maybe (throwError $ "missing case in right" <+> prettyLabel l) return $ lookupEnumList i ys
                    convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) (var IZ @@ EIx i)) x y

                return (vswh ctx.size h m1 xs, vemb (vapp ctx.size Ecit m (vemb h)))

            _ -> TODO

    go (VDeI sp1 m1 t1 s1 r1) (VDeI sp2 m2 t2 s2 r2) = do
        (h, ty) <- go sp1 sp2
        case force ty of
            VDsc -> do
                convTerm ctx (evalTerm ctx.size EmptyEnv         descIndMotive)  m1 m2
                let m :: VElim pass ctx
                    m = vann m1 $ varr VDsc Uni
                convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotive1) t1 t2
                convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotiveS) s1 s2
                convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotiveX) r1 r2
                return (vdei ctx.size h m1 t1 s1 r1, vemb (vapp ctx.size Ecit m (vemb h)))

            _ -> TODO

    go (VInd sp1 m1 c1) (VInd sp2 m2 c2) = do
        (h, ty) <- go sp1 sp2
        case force ty of
            VMuu d -> do
                convTerm ctx (VPie "_" Ecit (VMuu d) (Closure EmptyEnv Uni))      m1 m2
                let m :: VElim pass ctx
                    m = vann m1 $ varr (VMuu d) Uni

                    d' :: VElim pass ctx
                    d' = vann d VDsc

                convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim d' :> velim m) muMotiveT) c1 c2
                return (vind ctx.size h m1 c1, vemb (vapp ctx.size Ecit m (vemb h)))

            _ -> TODO

    go (VSpl sp1) (VSpl sp2) = do
        (h, ty) <- go sp1 sp2
        case force ty of
            VCod a -> 
                return (vspl ctx.size h, vsplCodArg ctx.size a)

            _ -> TODO

    go x y =
        throwError $ "last eliminator mismatch" <+> prettySpinePart ctx x <+> "/=" <+> prettySpinePart ctx y

spineLength :: Spine pass ctx -> Int
spineLength = go 0 where
    go !n VNil              = n
    go !n (VApp sp _ _)     = go (n + 1) sp
    go !n (VSel sp _)       = go (n + 1) sp
    go !n (VSwh sp _ _)     = go (n + 1) sp
    go !n (VDeI sp _ _ _ _) = go (n + 1) sp
    go !n (VInd sp _ _)     = go (n + 1) sp
    go !n (VSpl sp)         = go (n + 1) sp

prettySpinePart :: ConvCtx pass ctx -> Spine pass ctx -> Doc
prettySpinePart ctx (VApp _sp Ecit v)  = "application" <+> prettyVTermCtx ctx v
prettySpinePart ctx (VApp _sp Icit v)  = "application" <+> ppBraces (prettyVTermCtx ctx v)
prettySpinePart _   (VSel _sp s)       = "selector" <+> prettySelector s
prettySpinePart _   (VSwh _sp _ _)     = "switch"
prettySpinePart _   (VDeI _sp _ _ _ _) = "indDesc"
prettySpinePart _   (VInd _sp _ _)     = "ind"
prettySpinePart _   (VSpl _sp)         = "splice"
prettySpinePart _   VNil               = "none"

-------------------------------------------------------------------------------
-- Syntactical
-------------------------------------------------------------------------------

convSTerm :: Natural -> ConvCtx pass ctx -> VTerm pass ctx -> STerm pass ctx -> STerm pass ctx -> ConvM ()
convSTerm l env ty x y = convSTerm' l env ty x y

convSTerm' :: Natural -> ConvCtx pass ctx -> VTerm pass ctx -> STerm pass ctx -> STerm pass ctx -> ConvM ()
convSTerm' l env    _       (SEmb x)           (SEmb y) =
    void (convSElim' l env x y)

convSTerm' _ _      VUni    SUni               SUni =
    return ()
convSTerm' _ _      VUni    SOne               SOne =
    return ()
convSTerm' l ctx    VUni    (SPie x i a1 a b1) (SPie _ j a2 _ b2) = do
    convIcit ctx i j
    convSTerm' l ctx VUni a1 a2
    convSTerm' l (bind x a ctx) VUni (runSTZ l ctx.size b1) (runSTZ l ctx.size b2)
convSTerm' l ctx ty@VUni    a                  b =
    notConvertibleST l ctx ty a b

-- TODO
convSTerm' l env ty@VPie {} a                  b =
    notConvertibleST l env ty a b

-- TODO
convSTerm' l env ty@VSgm {} a                  b =
    notConvertibleST l env ty a b

convSTerm' _ _      VOne    STht               STht =
    return ()
convSTerm' l env ty@VOne    a                  b =
    notConvertibleST l env ty a b

-- TODO
convSTerm' _ _      (VFin _) (SEIx x)          (SEIx y)
    | x == y = return ()
convSTerm' l env ty@VFin {}  a                 b =
    notConvertibleST l env ty a b

-- TODO
convSTerm' l env ty@VDsc {} a                  b =
    notConvertibleST l env ty a b

-- TODO
convSTerm' l env ty@VMuu {} a                  b =
    notConvertibleST l env ty a b

-- TODO
convSTerm' l env ty@VCod {} a                  b =
    notConvertibleST l env ty a b

convSTerm' l env ty@VEmb {} a                  b =
    notConvertibleST l env ty a b

-- value constructors cannot be types
convSTerm' _ ctx ty@VLam {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VDe1 {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VDeS {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VDeX {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VCon {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VMul {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VEIx {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VQuo {} _ _ = notType ctx ty
convSTerm' _ ctx ty@VTht {} _ _ = notType ctx ty

convSElim' :: Natural -> ConvCtx pass ctx -> SElim pass ctx -> SElim pass ctx -> ConvM (VTerm pass ctx)
convSElim' _ _ (SErr err) _ = throwError $ ppStr $ show err
convSElim' _ _ _ (SErr err) = throwError $ ppStr $ show err

convSElim' _ env (SGbl x) (SGbl y)
    | x.name == y.name
    = return (sinkSize env.size (coeNoMetasVTerm x.typ))
convSElim' l env a@SGbl {} b = notConvertibleSE l env a b

convSElim' _ env (SVar x) (SVar y)
    | x == y
    = return (lookupEnv (lvlToIdx env.size x) env.types)

    | otherwise
    = mismatch "variable" (prettyName (lookupLvl env x)) (prettyName (lookupLvl env y))
convSElim' l env a@SVar {} b = notConvertibleSE l env a b

convSElim' _      env (SSpN t)   (SSpN s) = do
    ty <- convNeut env t s
    case force ty of
        VCod a -> return (vsplCodArg env.size a)
        _ -> throwError ("splice argument does not have Code-type" <+> ppSep
            [ "actual:" <+> prettyVTermCtx env ty
            ])
convSElim' l env a@SSpN {} b = notConvertibleSE l env a b

convSElim' NZ     _env (SSpl _ _x) (SSpl _ _y) = do
    throwError "nope"
convSElim' (NS l) env (SSpl x _) (SSpl y _) = do
    ty <- convSElim' l env x y
    return (vsplCodArg env.size ty)
convSElim' l env a@SSpl {} b = notConvertibleSE l env a b

convSElim' l      ctx (SApp i f t v) (SApp j g s _) = do
    convIcit ctx i j
    ty <- convSElim' l ctx f g
    case force ty of
        VPie _ _i a b -> do
            convSTerm' l ctx a t s
            return (run ctx.size b (vann v ty))
        _             -> throwError ("Function application head does not have a pi-type" <+> ppSep
            [ "actual:" <+> prettyVTermCtx ctx ty
            ])
convSElim' l      env a@SApp {} b = notConvertibleSE l env a b

-- TODO
convSElim' l      env a@SSel {} b = notConvertibleSE l env a b

-- TODO
convSElim' l      env a@SDeI {} b = notConvertibleSE l env a b

-- TODO
convSElim' l      env a@SInd {} b = notConvertibleSE l env a b

-- TODO
convSElim' l      env a@SSwh {} b = notConvertibleSE l env a b

convSElim' l      env (SLet _ t u) (SLet _ s v) = do
    ty <- convSElim' l env t s
    (env', r) <- newRigid env ty
    let x = EvalElim (VErr TODO) (SRgd r)
    convSElim' l env' (runSE l env.size u x) (runSE l env.size v x)
convSElim' l      env a@SLet {} b = notConvertibleSE l env a b

convSElim' _ env (SRgd x) (SRgd y)
    | x == y
    = case lookupRigidMap x env.rigids of
            Just ty -> return ty
            Nothing -> throwError ("rigid variable without a type")
convSElim' l      env a@SRgd {} b = notConvertibleSE l env a b

convSElim' l      env (SAnn t a v) (SAnn s b _) = do
    convSTerm' l env VUni a b
    convSTerm' l env v    t s
    return v
convSElim' l      env a@SAnn {} b = notConvertibleSE l env a b
