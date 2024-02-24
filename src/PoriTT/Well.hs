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
    WTcT :: Term pass ctx -> Well (HasTerms pass) ctx
    WLoc :: Loc -> Well pass ctx -> Well pass ctx

deriving instance Show (Well pass ctx)

-------------------------------------------------------------------------------
-- Renaming
-------------------------------------------------------------------------------

instance Renamable (Well pass) where rename = defaultRename; weaken = defaultWeaken

instance RenamableA (Well pass) where
    grename r (WLam x i t)     = WLam x i <$> grename (keep r) t
    grename r (WPie x i a b)   = WPie x i <$> grename r a <*> grename (keep r) b
    grename r (WSgm x i a b)   = WSgm x i <$> grename r a <*> grename (keep r) b
    grename _ WUni             = pure WUni
    grename _ WOne             = pure WOne
    grename _ WTht             = pure WTht
    grename _ (WHol n)         = pure (WHol n)
    grename _ WDsc             = pure WDsc
    grename _ WDe1             = pure WDe1
    grename r (WDeS t s)       = WDeS <$> grename r t <*> grename r s
    grename r (WDeX t)         = WDeX <$> grename r t
    grename r (WDeI d m x y z) = WDeI <$> grename r d <*> grename r m <*> grename r x <*> grename r y <*> grename r z
    grename r (WVar i)         = WVar <$> grename r i
    grename _ (WGbl g)         = pure (WGbl g)
    grename r (WLbl l ts)      = WLbl l <$> traverse (grename r) ts
    grename r (WEIx i ts)      = WEIx i <$> traverse (grename r) ts
    grename _ (WFin ls)        = pure (WFin ls)
    grename r (WApp i f t)     = WApp i <$> grename r f <*> grename r t
    grename r (WSel e s)       = flip WSel s <$> grename r e
    grename r (WAnn t s)       = WAnn <$> grename r t <*> grename r s
    grename r (WSwh e m ts)    = WSwh <$> grename r e <*> grename r m <*> traverse (traverse (grename r)) ts
    grename r (WLet x t s)     = WLet x <$> grename r t <*> grename (keep r) s
    grename r (WMul i t s)     = WMul i <$> grename r t <*> grename r s
    grename r (WMuu d)         = WMuu <$> grename r d
    grename r (WCon t)         = WCon <$> grename r t
    grename r (WCod t)         = WCod <$> grename r t
    grename r (WQuo t)         = WQuo <$> grename r t
    grename r (WSpl t)         = WSpl <$> grename r t
    grename r (WInd e m c)     = WInd <$> grename r e <*> grename r m <*> grename r c
    grename r (WLst ts)        = WLst <$> traverse (grename r) ts
    grename r (WTcT t)         = WTcT <$> grename r t
    grename r (WLoc l t)       = WLoc l <$> grename r t
    grename _ WSkp             = pure WSkp

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
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        , i == Ecit
        = RArr (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RPie x' i (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (WSgm x i a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
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
    toRaw ns env (WTcT t)         = toRaw ns env t
    toRaw _  _   WSkp             = RSkp
    toRaw ns env (WLoc _ t)       = toRaw ns env t
