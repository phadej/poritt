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
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Nice
import PoriTT.PP
import PoriTT.Quote
import PoriTT.Term
import PoriTT.Used
import PoriTT.Value

-- | Conversion context.
data ConvCtx ctx = ConvCtx
    { size   :: Size ctx
    , names  :: Env ctx Name
    , types  :: Env ctx (VTerm NoMetas ctx)
    , nscope :: NameScope
    }

bind :: Name -> VTerm NoMetas ctx -> ConvCtx ctx -> ConvCtx (S ctx)
bind x t (ConvCtx s xs ts gs) = ConvCtx (SS s) (xs :> x) (mapSink ts :> sink t) gs

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
mkConvCtx :: Size ctx -> Env ctx Name -> Env ctx (VTerm NoMetas ctx) -> NameScope -> ConvCtx ctx
mkConvCtx = ConvCtx

prettyVTermCtx :: ConvCtx ctx -> VTerm NoMetas ctx -> Doc
prettyVTermCtx ctx = prettyVTerm ctx.size ctx.nscope ctx.names

lookupLvl :: ConvCtx ctx -> Lvl ctx -> Name
lookupLvl ctx l = lookupEnv (lvlToIdx ctx.size l) ctx.names

mismatch :: Doc -> Doc -> Doc -> Either Doc a
mismatch t x y = Left $ t <+> "mismatch:" <+> x <+> "/=" <+> y

notConvertible :: ConvCtx ctx -> VTerm NoMetas ctx -> VTerm NoMetas ctx -> VTerm NoMetas ctx -> Either Doc ()
notConvertible ctx ty x y = Left $ ppSep
    [ "not convertible:"
    , prettyVTermCtx ctx ty <+> ":"
    , prettyVTermCtx ctx x <+> "/="
    , prettyVTermCtx ctx y
    ]

notType :: ConvCtx ctx -> VTerm NoMetas ctx -> Either Doc ()
notType ctx ty = Left $ ppSep
    [ "CONV PANIC: NOT A TYPE"
    , prettyVTermCtx ctx ty
    ]

-- | Beta-eta conversion checking of terms.
--
-- The last argument is a common type of the terms.
-- The conversion checking is (somewhat) type-directed, we need
-- types for do eta-expansion.
--
convTerm :: ConvCtx ctx -> VTerm NoMetas ctx -> VTerm NoMetas ctx -> VTerm NoMetas ctx -> Either Doc ()
convTerm ctx ty x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    convTerm' ctx ty x y

-- | Beta-eta conversion checking of eliminations.
convElim :: ConvCtx ctx -> VElim NoMetas ctx -> VElim NoMetas ctx -> Either Doc ()
convElim ctx x y = do
    -- we define a helper function, so we can trace when needed.
    -- traceM $ "CONV: " ++ show (ppSep [prettyVTermCtx ctx ty, " |-" <+> prettyVTermCtx ctx x, "=?=" <+> prettyVTermCtx ctx y])
    convElim' ctx x y

-------------------------------------------------------------------------------
-- Workers
-------------------------------------------------------------------------------

convIcit :: ConvCtx ctx -> Icit -> Icit -> Either Doc ()
convIcit _ctx i j
    | i == j    = return ()
    | otherwise = mismatch "icity" (prettyIcit i) (prettyIcit j)

convTerm' :: ConvCtx ctx -> VTerm NoMetas ctx -> VTerm NoMetas ctx -> VTerm NoMetas ctx -> Either Doc ()
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
convTerm' ctx VUni (VEmb (VRgd x sp1)) (VEmb (VRgd y sp2))   = convNeutral ctx x sp1 y sp2
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
convTerm' ctx (VFin _)  (VEmb x)     (VEmb y)     = convElim ctx x y
convTerm' ctx (VFin ls) x            y            = notConvertible ctx (VFin ls) x y

-- ⊢ Desc ∋ t ≡ s
convTerm' _   VDsc VDe1           VDe1           = pure ()
convTerm' ctx VDsc (VDeS t1 s1)   (VDeS t2 s2)   = do
    convTerm ctx VUni t1 t2
    convTerm ctx (VPie "S" Ecit t1 (Closure EmptyEnv Dsc)) s1 s2
convTerm' ctx VDsc (VDeX t1)      (VDeX t2)      = do
    convTerm ctx VDsc t1 t2
convTerm' ctx VDsc (VEmb x)       (VEmb y)       = convElim ctx x y
convTerm' ctx VDsc x              y              = notConvertible ctx VDsc x y

-- ⊢ μ d ∋ t ≡ s
convTerm' ctx (VMuu d) (VCon x)       (VCon y)     = do
    let xty = vapps ctx.size (vgbl ctx.size evalDescGlobal) [d, VMuu d]
    convTerm ctx (vemb xty) x y
convTerm' ctx (VMuu _) (VEmb x)       (VEmb y)     = convElim ctx x y
convTerm' ctx (VMuu d) x              y            = notConvertible ctx (VMuu d) x y

-- ⊢ Code a ∋ t ≡ s
convTerm' ctx (VCod a) (VQuo x _)     (VQuo y _)   = do
    convSTerm NZ ctx a x y
convTerm' ctx (VCod _) (VEmb x)       (VEmb y)     = convElim ctx x y
convTerm' ctx (VCod a) x              y            = notConvertible ctx (VCod a) x y

-- Only neutral terms can be convertible under neutral type
convTerm' ctx (VEmb VRgd {})     (VEmb x) (VEmb y) = convElim ctx x y
convTerm' ctx (VEmb (VRgd h sp)) x y = notConvertible ctx (VEmb (VRgd h sp)) x y

convTerm' _   (VEmb (VErr msg)) _ _ = Left $ ppStr $ show msg

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

convElim' :: ConvCtx ctx -> VElim NoMetas ctx -> VElim NoMetas ctx -> Either Doc ()
-- Globals
convElim' _  (VGbl g1 VNil _) (VGbl g2 VNil _)
    | g1.name == g2.name   = pure ()
-- otherwise we check the values
convElim' ctx (VGbl _ _ t)   u             = convElim ctx t u
convElim' ctx t              (VGbl _ _ u)  = convElim ctx t u
convElim' ctx (VRgd h1 sp1)  (VRgd h2 sp2) = convNeutral ctx h1 sp1 h2 sp2
convElim' ctx (VAnn t ty)    e             = convTerm ctx ty t (vemb e)
convElim' ctx e              (VAnn t ty)   = convTerm ctx ty (vemb e) t
convElim' _   (VErr msg)     _             = Left $ ppStr $ show msg
convElim' _   _              (VErr msg)    = Left $ ppStr $ show msg

-- Eta expand value of function type.
etaLam :: Size ctx -> Icit -> VElim NoMetas ctx -> VTerm NoMetas (S ctx)
etaLam s i f = vemb (vapp (SS s) i (sink f) (vemb (valZ s)))

convNeutral :: ConvCtx ctx -> Lvl ctx -> Spine NoMetas ctx -> Lvl ctx -> Spine NoMetas ctx -> Either Doc ()
convNeutral ctx x sp1 y sp2
    | x == y    = do
        -- traceM "convNeutral"
        -- traceM $ show $ prettyVTermCtx ctx (VRgd x sp1)
        -- traceM $ show $ prettyVTermCtx ctx (VRgd y sp2)
        -- traceM $ show $ prettyVTermCtx ctx headTy
        convSpine ctx x sp1 sp2
    | otherwise = mismatch "spine head" (prettyName (lookupLvl ctx x)) (prettyName (lookupLvl ctx y))

convSpine :: forall ctx. ConvCtx ctx -> Lvl ctx -> Spine NoMetas ctx -> Spine NoMetas ctx -> Either Doc ()
convSpine ctx headLvl sp1' sp2' = do
    bwd [] sp1' sp2'
  where
    headTy = lookupEnv (lvlToIdx ctx.size headLvl) ctx.types

    bwd :: [(SpinePart ctx, SpinePart ctx)] -> Spine NoMetas ctx -> Spine NoMetas ctx -> Either Doc ()
    bwd acc sp1 sp2 = case (unsnocSpine sp1, unsnocSpine sp2) of
        (Nothing, Nothing)           -> void $ foldParts fwd (VRgd headLvl VNil, headTy) acc
        (Just (xs, x), Just (ys, y)) -> bwd ((x,y) : acc) xs ys
        _                            -> mismatch "spine length" (ppInt (spineLength sp1')) (ppInt (spineLength sp2'))

    fwd :: (VElim NoMetas ctx, VTerm NoMetas ctx) -> SpinePart ctx -> SpinePart ctx -> Either Doc (VElim NoMetas ctx, VTerm NoMetas ctx)
    fwd (sp, (VEmb (VGbl _ _ t))) x           y =
        fwd (sp, vemb t) x y

    fwd (sp, VPie _ _ a b) (PApp i x)    (PApp j y) = do
        convIcit ctx i j
        convTerm ctx a x y
        return (vapp ctx.size i sp x, run ctx.size b (vann x a))

    fwd (sp, VSgm _ _ a b) (PSel x)    (PSel y)
        | x == y = case x of
            "fst" -> return (vsel ctx.size sp x, a)
            "snd" -> return (vsel ctx.size sp x, run ctx.size b (vsel ctx.size sp "fst"))
            _     -> Left $ "conv panic: sigma with" <+> prettySelector x
        | otherwise                            = mismatch "selector" (prettySelector x) (prettySelector y)

    fwd (sp, VFin ls)    (PSwh m1 xs) (PSwh m2 ys)
        | length xs /= length ys               = mismatch "switch case arity" (ppInt (length xs)) (ppInt (length ys))
        | otherwise                            = do
            convTerm ctx (VPie "_" Ecit (VFin ls) (Closure EmptyEnv Uni)) m1 m2
            let m :: VElim NoMetas ctx
                m = vann m1 $ varr (VFin ls) Uni

            ifor_ ls $ \i' l -> do
                let i = EnumIdx i'
                x <- maybe (Left $ "missing case in left"  <+> prettyLabel l) return $ lookupEnumList i xs
                y <- maybe (Left $ "missing case in right" <+> prettyLabel l) return $ lookupEnumList i ys
                convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) (var IZ @@ EIx i)) x y

            return (vswh ctx.size sp m1 xs, vemb (vapp ctx.size Ecit m (vemb sp)))

    fwd (sp, VDsc)   (PDeI m1 t1 s1 r1)
                     (PDeI m2 t2 s2 r2)        = do
        convTerm ctx (evalTerm ctx.size EmptyEnv         descIndMotive)  m1 m2
        let m :: VElim NoMetas ctx
            m = vann m1 $ varr VDsc Uni
        convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotive1) t1 t2
        convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotiveS) s1 s2
        convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim m) descIndMotiveX) r1 r2
        return (vdei ctx.size sp m1 t1 s1 r1, vemb (vapp ctx.size Ecit m (vemb sp)))

    fwd (sp, VMuu d)     (PInd m1 c1) (PInd m2 c2) = do
        convTerm ctx (VPie "_" Ecit (VMuu d) (Closure EmptyEnv Uni))      m1 m2
        let m :: VElim NoMetas ctx
            m = vann m1 $ varr (VMuu d) Uni

            d' :: VElim NoMetas ctx
            d' = vann d VDsc

        convTerm ctx (evalTerm ctx.size (EmptyEnv :> velim d' :> velim m) muMotiveT) c1 c2
        return (vind ctx.size sp m1 c1, vemb (vapp ctx.size Ecit m (vemb sp)))

    fwd (sp, VCod a)        PSpl         PSpl         =
        -- Left $ "eliminator todo" <+> prettyVTermCtx ctx a -- TODO
        return (vspl ctx.size sp, vsplCodArg ctx.size a)

    fwd (_sp, ty)        x            y            =
        Left $ "eliminator mismatch" <+> prettyVTermCtx ctx ty <+> "|-" <+> prettySpinePart ctx x <+> "/=" <+> prettySpinePart ctx y

foldParts :: Monad m => (a -> b -> b -> m a) -> a -> [(b,b)] -> m a
foldParts _ a []         = return a
foldParts f a ((x,y):zs) = f a x y >>= \b -> foldParts f b zs

unsnocSpine :: Spine NoMetas ctx -> Maybe (Spine NoMetas ctx, SpinePart ctx)
unsnocSpine VNil                 = Nothing
unsnocSpine (VApp sp i x)        = Just (sp, PApp i x)
unsnocSpine (VSel sp x)          = Just (sp, PSel x)
unsnocSpine (VSwh sp m ts)       = Just (sp, PSwh m ts)
unsnocSpine (VDeI sp m c1 c2 c3) = Just (sp, PDeI m c1 c2 c3)
unsnocSpine (VInd sp m c)        = Just (sp, PInd m c)
unsnocSpine (VSpl sp)            = Just (sp, PSpl)
{-
snocSpine :: Spine NoMetas ctx -> SpinePart ctx -> Spine NoMetas ctx
snocSpine sp (SApp x)          = VApp sp x
snocSpine sp (SSel s)          = VSel sp s
snocSpine sp (SSwh m ts)       = VSwh sp m ts
snocSpine sp (SDeI m c1 c2 c3) = VDeI sp m c1 c2 c3
snocSpine sp (SInd m t)        = VInd sp m t
-}

spineLength :: Spine NoMetas ctx -> Int
spineLength = go 0 where
    go !n VNil              = n
    go !n (VApp sp _ _)     = go (n + 1) sp
    go !n (VSel sp _)       = go (n + 1) sp
    go !n (VSwh sp _ _)     = go (n + 1) sp
    go !n (VDeI sp _ _ _ _) = go (n + 1) sp
    go !n (VInd sp _ _)     = go (n + 1) sp
    go !n (VSpl sp)         = go (n + 1) sp

-- /Verterbrae/
data SpinePart ctx
    = PApp !Icit (VTerm NoMetas ctx)
    | PSel !Selector
    | PSwh (VTerm NoMetas ctx) (EnumList (VTerm NoMetas ctx))
    | PDeI (VTerm NoMetas ctx) (VTerm NoMetas ctx) (VTerm NoMetas ctx) (VTerm NoMetas ctx)
    | PInd (VTerm NoMetas ctx) (VTerm NoMetas ctx)
    | PSpl
  deriving Show

prettySpinePart :: ConvCtx ctx -> SpinePart ctx -> Doc
prettySpinePart ctx (PApp Ecit v)  = "application" <+> prettyVTermCtx ctx v
prettySpinePart ctx (PApp Icit v)  = "application" <+> ppBraces (prettyVTermCtx ctx v)
prettySpinePart _   (PSel s)       = "selector" <+> prettySelector s
prettySpinePart _   (PSwh _ _)     = "switch"
prettySpinePart _   (PDeI _ _ _ _) = "indDesc"
prettySpinePart _   (PInd _ _)     = "ind"
prettySpinePart _   PSpl           = "splice"

convSTerm :: Natural -> ConvCtx ctx -> VTerm NoMetas ctx -> STerm NoMetas ctx -> STerm NoMetas ctx -> Either Doc ()
convSTerm l env (VQuo ty _) x y = convSTerm' l env ty x y
convSTerm _ _   ty          x y = Left $ "convSTerm not convertible " <> ppStr (show (ty, x ,y))

convSTerm' :: Natural -> ConvCtx ctx -> STerm 'NoMetas ctx -> STerm 'NoMetas ctx -> STerm 'NoMetas ctx -> Either Doc ()
convSTerm' l env _ty (SEmb x) (SEmb y) = convSElim' l env x y
convSTerm' _ _ _ (SEIx x) (SEIx y)
    | x == y = return ()
convSTerm' _ _   SUni SUni SUni = return ()
convSTerm' _ _   SUni SOne SOne = return ()
convSTerm' l ctx SUni (SPie x i a1 b1) (SPie _ j a2 b2) = do
    convIcit ctx i j
    convSTerm' l ctx SUni a1 a2
    -- TODO check b1 b2
convSTerm' _ _ ty x y = Left $ "convSTerm not convertible" <> ppStr (show (ty, x, y))

convSElim' :: Natural -> ConvCtx ctx -> SElim NoMetas ctx -> SElim NoMetas ctx -> Either Doc ()
convSElim' _ _ (SGbl x) (SGbl y)
    | x.name == y.name
    = return ()
-- convSElim' env (SElm x) (SElm y) = convElim env x y
convSElim' _ env (SVar x) (SVar y)
    | x == y
    = return ()

    | otherwise
    = mismatch "variable" (prettyName (lookupLvl env x)) (prettyName (lookupLvl env y))

convSElim' NZ     env (SSpl _ x) (SSpl _ y) = convElim env x y
convSElim' (NS l) env (SSpl x _) (SSpl y _) = convSElim' l env x y
convSElim' l      ctx (SApp i f x) (SApp j g y) = do
  convIcit ctx i j
  convSElim' l ctx f g
  -- TODO: check x y
convSElim' _ env x y = Left $ "TODO: convSElim not convertible " <> ppStr ("\n" ++ show x ++ "\n" ++ show y)
