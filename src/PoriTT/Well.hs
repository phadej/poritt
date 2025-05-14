module PoriTT.Well (
    WellPass (..),
    Well (..),
    substWell,
    prettyWell,
) where

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Loc
import PoriTT.Name
import PoriTT.PP
import PoriTT.Raw
import PoriTT.Term

-- | Well scoped term variants
data WellPass
    = HasTerms TermPass -- ^ could have embedded 'Term's.
    | NoTerms           -- ^ doesn't have embedded 'Term's, used for macro bodies.

-- | Well scoped terms.
type Well :: WellPass -> Ctx -> Type
data Well pass ctx where
    WLam :: Name -> Icit -> Well pass (S ctx) -> Well pass ctx
    WPie :: Name -> Icit -> Well pass ctx -> Well pass (S ctx) -> Well pass ctx
    WSgm :: Name -> Icit -> Well pass ctx -> Well pass (S ctx) -> Well pass ctx
    WMul :: Icit -> Well pass ctx -> Well pass ctx -> Well pass ctx
    WOne :: Well pass ctx
    WTht :: Well pass ctx
    WUni :: Well pass ctx
    WVar :: Idx ctx -> Well pass ctx
    WGbl :: Global -> Well pass ctx
    WApp :: Icit -> Well pass ctx -> Well pass ctx -> Well pass ctx
    WSel :: Well pass ctx -> Selector -> Well pass ctx
    WSwh :: Well pass ctx -> Well pass ctx -> [Either Label EnumIdx := Well pass ctx] -> Well pass ctx
    WAnn :: Well pass ctx -> Well pass ctx -> Well pass ctx
    WLet :: Name -> Well pass ctx -> Well pass (S ctx) -> Well pass ctx
    WLbl :: Label -> [Well pass ctx] -> Well pass ctx
    WEIx :: EnumIdx -> [Well pass ctx] -> Well pass ctx
    WFin :: [Label] -> Well pass ctx
    WDsc :: Well pass ctx
    WDe1 :: Well pass ctx
    WDeS :: Well pass ctx -> Well pass ctx -> Well pass ctx
    WDeX :: Well pass ctx -> Well pass ctx
    WDeI :: Well pass ctx -> Well pass ctx -> Well pass ctx -> Well pass ctx -> Well pass ctx -> Well pass ctx
    WMuu :: Well pass ctx -> Well pass ctx
    WCon :: Well pass ctx -> Well pass ctx
    WInd :: Well pass ctx -> Well pass ctx -> Well pass ctx -> Well pass ctx
    WCod :: Well pass ctx -> Well pass ctx
    WQuo :: Well pass ctx -> Well pass ctx
    WSpl :: Well pass ctx -> Well pass ctx
    WHol :: Name -> Well pass ctx
    WSkp :: Well pass ctx
    WLst :: [Well pass ctx] -> Well pass ctx
    WLoc :: Loc -> Well pass ctx -> Well pass ctx

deriving instance Show (Well pass ctx)

-------------------------------------------------------------------------------
-- Renaming
-------------------------------------------------------------------------------

instance Weaken (Well pass) where
    weaken r (WLam x i t)     = WLam x i (weaken (keep r) t)
    weaken r (WPie x i a b)   = WPie x i (weaken r a) (weaken (keep r) b)
    weaken r (WSgm x i a b)   = WSgm x i (weaken r a) (weaken (keep r) b)
    weaken _ WUni             = WUni
    weaken _ WOne             = WOne
    weaken _ WTht             = WTht
    weaken _ (WHol n)         = WHol n
    weaken _ WDsc             = WDsc
    weaken _ WDe1             = WDe1
    weaken r (WDeS t s)       = WDeS (weaken r t) (weaken r s)
    weaken r (WDeX t)         = WDeX (weaken r t)
    weaken r (WDeI d m x y z) = WDeI (weaken r d) (weaken r m) (weaken r x) (weaken r y) (weaken r z)
    weaken r (WVar i)         = WVar (weaken r i)
    weaken _ (WGbl g)         = WGbl g
    weaken r (WLbl l ts)      = WLbl l (fmap (weaken r) ts)
    weaken r (WEIx i ts)      = WEIx i (fmap (weaken r) ts)
    weaken _ (WFin ls)        = WFin ls
    weaken r (WApp i f t)     = WApp i(weaken r f) (weaken r t)
    weaken r (WSel e s)       = WSel (weaken r e) s
    weaken r (WAnn t s)       = WAnn (weaken r t) (weaken r s)
    weaken r (WSwh e m ts)    = WSwh (weaken r e) (weaken r m) (fmap (fmap (weaken r)) ts)
    weaken r (WLet x t s)     = WLet x (weaken r t) (weaken (keep r) s)
    weaken r (WMul i t s)     = WMul i (weaken r t) (weaken r s)
    weaken r (WMuu d)         = WMuu (weaken r d)
    weaken r (WCon t)         = WCon (weaken r t)
    weaken r (WCod t)         = WCod (weaken r t)
    weaken r (WQuo t)         = WQuo (weaken r t)
    weaken r (WSpl t)         = WSpl (weaken r t)
    weaken r (WInd e m c)     = WInd (weaken r e) (weaken r m) (weaken r c)
    weaken r (WLst ts)        = WLst (fmap (weaken r) ts)
    weaken r (WLoc l t)       = WLoc l (weaken r t)
    weaken _ WSkp             = WSkp

instance Contract (Well pass) where
    contract r (WLam x i t)     = WLam x i <$> contract (keep r) t
    contract r (WPie x i a b)   = WPie x i <$> contract r a <*> contract (keep r) b
    contract r (WSgm x i a b)   = WSgm x i <$> contract r a <*> contract (keep r) b
    contract _ WUni             = pure WUni
    contract _ WOne             = pure WOne
    contract _ WTht             = pure WTht
    contract _ (WHol n)         = pure (WHol n)
    contract _ WDsc             = pure WDsc
    contract _ WDe1             = pure WDe1
    contract r (WDeS t s)       = WDeS <$> contract r t <*> contract r s
    contract r (WDeX t)         = WDeX <$> contract r t
    contract r (WDeI d m x y z) = WDeI <$> contract r d <*> contract r m <*> contract r x <*> contract r y <*> contract r z
    contract r (WVar i)         = WVar <$> contract r i
    contract _ (WGbl g)         = pure (WGbl g)
    contract r (WLbl l ts)      = WLbl l <$> traverse (contract r) ts
    contract r (WEIx i ts)      = WEIx i <$> traverse (contract r) ts
    contract _ (WFin ls)        = pure (WFin ls)
    contract r (WApp i f t)     = WApp i <$> contract r f <*> contract r t
    contract r (WSel e s)       = flip WSel s <$> contract r e
    contract r (WAnn t s)       = WAnn <$> contract r t <*> contract r s
    contract r (WSwh e m ts)    = WSwh <$> contract r e <*> contract r m <*> traverse (traverse (contract r)) ts
    contract r (WLet x t s)     = WLet x <$> contract r t <*> contract (keep r) s
    contract r (WMul i t s)     = WMul i <$> contract r t <*> contract r s
    contract r (WMuu d)         = WMuu <$> contract r d
    contract r (WCon t)         = WCon <$> contract r t
    contract r (WCod t)         = WCod <$> contract r t
    contract r (WQuo t)         = WQuo <$> contract r t
    contract r (WSpl t)         = WSpl <$> contract r t
    contract r (WInd e m c)     = WInd <$> contract r e <*> contract r m <*> contract r c
    contract r (WLst ts)        = WLst <$> traverse (contract r) ts
    contract r (WLoc l t)       = WLoc l <$> contract r t
    contract _ WSkp             = pure WSkp

-------------------------------------------------------------------------------
-- Subst
-------------------------------------------------------------------------------

instance Var (Well pass) where
    var = WVar

-- | Substitute any well scoped terms into well scoped term without embedded terms.
--
-- This is more general than 'subst'.
--
substWell :: Sub (Well pass) ctx ctx' -> Well NoTerms ctx -> Well pass ctx'
substWell sub (WVar x)     = substIdx sub x
substWell sub (WApp i f t) = WApp i (substWell sub f) (substWell sub t)
substWell sub (WLbl l ts)  = WLbl l (substWell sub <$> ts)
substWell sub (WMul i t s) = WMul i (substWell sub t) (substWell sub s)
substWell sub (WCon t)     = WCon (substWell sub t)
substWell sub (WLoc _ t)   = substWell sub t
substWell sub (WLam n i w) = WLam n i (substWell (keepSub sub) w)
substWell sub (WLst ts)    = WLst (substWell sub <$> ts)
substWell _   (WGbl g)     = WGbl g
substWell _   WOne         = WOne
substWell _   WTht         = WTht
substWell _   WUni         = WUni
substWell _   WDsc         = WDsc
substWell _   WDe1         = WDe1
substWell _   (WHol n)     = (WHol n)
substWell _   WSkp         = WSkp

substWell _ WPie {}        = TODO
substWell _ WSgm {}        = TODO
substWell _ WSel {}        = TODO
substWell _ WSwh {}        = TODO
substWell _ WAnn {}        = TODO
substWell _ WLet {}        = TODO
substWell _ WEIx {}        = TODO
substWell _ WFin {}        = TODO
substWell _ WDeS {}        = TODO
substWell _ WDeX {}        = TODO
substWell _ WDeI {}        = TODO
substWell _ WMuu {}        = TODO
substWell _ WInd {}        = TODO
substWell _ WCod {}        = TODO
substWell _ WQuo {}        = TODO
substWell _ WSpl {}        = TODO

instance Subst (Well NoTerms) where
    subst = substWell


-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

prettyWell :: NameScope -> Env ctx Name -> Int -> Well pass ctx -> Doc
prettyWell ns env d x = prettyRaw d (toRaw ns env x)

instance ToRaw (Well pass) where
    toRaw ns env (WLam x i t)
        = withFreshName ns x $ \ns' x' ->
          RLam x' i (toRaw ns' (env :> x') t)
    toRaw ns env (WPie x i a b)
        | Just b' <- contract unusedIdx b
        , i == Ecit
        = RArr (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RPie x' i (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (WSgm x i a b)
        | Just b' <- contract unusedIdx b
        , i == Ecit
        = RPrd (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RSgm x' i (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (WLet x t s)
        = withFreshName ns x $ \ns' x' ->
          RLet x' (toRaw ns env t) (toRaw ns' (env :> x') s)

    toRaw ns env (WMul i t s)     = RMul i (toRaw ns env t) (toRaw ns env s)
    toRaw _  _   WUni             = RUni
    toRaw ns env (WLbl l ts)      = rapps (RLbl l) (toRaw ns env <$> ts)
    toRaw ns env (WEIx i ts )     = rapps (REIx i) (toRaw ns env <$> ts)
    toRaw _  _   (WFin ls)        = RFin ls
    toRaw _  env (WVar i)         = RVar (lookupEnv i env)
    toRaw _  _   (WGbl g)         = RGbl g
    toRaw ns env (WApp i f t)     = rapp i (toRaw ns env f) (toRaw ns env t)
    toRaw ns env (WSel e s)       = rsel (toRaw ns env e) s
    toRaw ns env (WSwh e m ts)    = RSwh (toRaw ns env e) (toRaw ns env m) (fmap (fmap (toRaw ns env)) ts)
    toRaw _  _   WOne             = ROne
    toRaw _  _   WTht             = RTht
    toRaw _  _   (WHol n)         = RHol n
    toRaw _  _   WDsc             = RDsc
    toRaw _  _   WDe1             = RDe1
    toRaw ns env (WDeS t s)       = RDeS (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (WDeX t)         = RDeX (toRaw ns env t)
    toRaw ns env (WDeI e m x y z) = RDeI (toRaw ns env e) (toRaw ns env m) (toRaw ns env x) (toRaw ns env y) (toRaw ns env z)
    toRaw ns env (WMuu d)         = RMuu (toRaw ns env d)
    toRaw ns env (WCon t)         = RCon (toRaw ns env t)
    toRaw ns env (WCod t)         = RCod (toRaw ns env t)
    toRaw ns env (WQuo t)         = RQuo (toRaw ns env t)
    toRaw ns env (WSpl t)         = RSpl (toRaw ns env t)
    toRaw ns env (WInd e m c)     = RInd (toRaw ns env e) (toRaw ns env m) (toRaw ns env c)
    toRaw ns env (WAnn t s)       = RAnn (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (WLst ts)        = RLst (toRaw ns env <$> ts)
    toRaw _  _   WSkp             = RSkp
    toRaw ns env (WLoc _ t)       = toRaw ns env t
