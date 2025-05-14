{-# LANGUAGE InstanceSigs #-}
module PoriTT.Term (
    TermPass (..),
    Term (..),
    Elim (..),
    prettyTerm,
    prettyElim,
    prettyElim',
    emb,
    ann,
    quo,
    spl,
    coeNoMetasElim,
    coeSizeElim,
    weakenTerm,
    weakenElim,
    qrenameTerm,
) where

import Unsafe.Coerce (unsafeCoerce)

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Icit
import PoriTT.Meta.Var
import PoriTT.Name
import PoriTT.PP
import PoriTT.Pruning
import PoriTT.Raw
import PoriTT.Rigid

import {-# SOURCE #-} PoriTT.Global (Global)

-- | Term pass
data TermPass
    = HasMetas  -- ^ could have 'MetaVar's, after elaboration.
    | NoMetas   -- ^ doesn't have 'MetaVar's, after type-checking or zonking.

-- | Term types are checked
type Term :: TermPass -> Ctx -> Type
data Term pass ctx where
    Pie :: Name -> !Icit -> Term pass ctx -> Term pass (S ctx) -> Term pass ctx
    Lam :: Name -> !Icit -> Term pass (S ctx) -> Term pass ctx
    Mul :: !Icit -> Term pass ctx -> Term pass ctx -> Term pass ctx
    Sgm :: Name -> !Icit -> Term pass ctx -> Term pass (S ctx) -> Term pass ctx
    EIx :: EnumIdx -> Term pass ctx
    Fin :: [Label] -> Term pass ctx
    Uni :: Term pass ctx
    One :: Term pass ctx
    Tht :: Term pass ctx
    Dsc :: Term pass ctx
    De1 :: Term pass ctx
    DeS :: Term pass ctx -> Term pass ctx -> Term pass ctx
    DeX :: Term pass ctx -> Term pass ctx
    Muu :: Term pass ctx -> Term pass ctx
    Con :: Term pass ctx -> Term pass ctx
    Cod :: Term pass ctx -> Term pass ctx
    Quo :: Term pass ctx -> Term pass ctx
    Emb :: Elim pass ctx -> Term pass ctx
    WkT :: Wk ctx ctx' -> Term pass ctx -> Term pass ctx'

-- | Elimination types are inferred
type Elim :: TermPass -> Ctx -> Type
data Elim pass ctx where
    Var :: Idx ctx -> Elim pass ctx
    Met :: MetaVar -> Qruning ctx -> Elim HasMetas ctx
    Rgd :: RigidVar ctx -> Elim pass ctx
    Gbl :: Global -> Elim pass ctx
    App :: Icit -> Elim pass ctx -> Term pass ctx -> Elim pass ctx
    Sel :: Elim pass ctx -> Selector -> Elim pass ctx
    Swh :: Elim pass ctx -> Term pass ctx -> EnumList (Term pass ctx) -> Elim pass ctx
    DeI :: Elim pass ctx -> Term pass ctx -> Term pass ctx -> Term pass ctx -> Term pass ctx -> Elim pass ctx
    Ind :: Elim pass ctx -> Term pass ctx -> Term pass ctx -> Elim pass ctx
    Spl :: Elim pass ctx -> Elim pass ctx
    Ann :: Term pass ctx -> Term pass ctx -> Elim pass ctx
    Let :: Name -> Elim pass ctx -> Elim pass (S ctx) -> Elim pass ctx
    WkE :: Wk ctx ctx' -> Elim pass ctx -> Elim pass ctx'

deriving instance Show (Term pass ctx)
deriving instance Show (Elim pass ctx)

-------------------------------------------------------------------------------
-- coercions
-------------------------------------------------------------------------------

-- | 'Elim' with no metas can be coerced to 'Elim' with metas.
coeNoMetasElim :: Elim NoMetas ctx -> Elim pass ctx
coeNoMetasElim = unsafeCoerce

coeSizeElim :: Elim pass EmptyCtx -> Elim pass ctx
coeSizeElim = unsafeCoerce

-------------------------------------------------------------------------------
-- Smart constructors
-------------------------------------------------------------------------------

-- | We need to do this, as quoteElim may unfold global terms.
emb :: Elim pass ctx -> Term pass ctx
emb (Ann t _) = t
emb e         = Emb e

-- | This is slightly wrong to do so
-- but we do similar simplification in conversion
-- so doing it here is justified.
ann :: Term pass ctx -> Term pass ctx -> Elim pass ctx
ann (Emb e) _ = e
ann t       a = Ann t a

quo :: Term pass ctx -> Term pass ctx
quo (Emb (Spl e)) = Emb e
quo t = Quo t

spl :: Elim pass ctx -> Elim pass ctx
spl (Ann (Quo t) (Cod a)) = Ann t a
spl e                     = Spl e

-------------------------------------------------------------------------------
-- Weakening
-------------------------------------------------------------------------------

instance Weaken (Term pass) where
    -- we have explicit weakening in the terms.
    -- it doesn't complicate evaluation nor linting,
    -- in these cases we don't end up traversing terms extra times.
    weaken w (WkT w' t) = WkT (compWk w' w) t
    weaken w t          = WkT w t

instance Weaken (Elim pass) where
    weaken w (WkE w' e) = WkE (compWk w' w) e
    weaken w (Var i)    = Var (weakenIdx w i)
    weaken w (Met m ts) = Met m (weakenQruning w ts)
    weaken _ (Gbl g)    = Gbl g
    weaken w e          = WkE w e

weakenTerm :: Wk ctx ctx' -> Term pass ctx -> Term pass ctx'
weakenTerm r (Lam x i t)   = Lam x i (weakenTerm (keep r) t)
weakenTerm r (Pie x i a b) = Pie x i (weakenTerm r a) (weakenTerm (keep r) b)
weakenTerm r (Sgm x i a b) = Sgm x i (weakenTerm r a) (weakenTerm (keep r) b)
weakenTerm r (Mul i t s)   = Mul i (weakenTerm r t) (weakenTerm r s)
weakenTerm _ Uni           = Uni
weakenTerm _ One           = One
weakenTerm _ Tht           = Tht
weakenTerm _ Dsc           = Dsc
weakenTerm _ De1           = De1
weakenTerm r (DeS t s)     = DeS (weakenTerm r t) (weakenTerm r s)
weakenTerm r (DeX t)       = DeX (weakenTerm r t)
weakenTerm r (Emb e)       = Emb (weakenElim r e)
weakenTerm _ (EIx i)       = EIx i
weakenTerm _ (Fin ls)      = Fin ls
weakenTerm r (Muu d)       = Muu (weakenTerm r d)
weakenTerm r (Con t)       = Con (weakenTerm r t)
weakenTerm r (Cod t)       = Cod (weakenTerm r t)
weakenTerm r (Quo t)       = Quo (weakenTerm r t)
weakenTerm r (WkT w t)     = weakenTerm (compWk w r) t

weakenElim :: Wk ctx ctx' -> Elim pass ctx -> Elim pass ctx'
weakenElim r (Var i)         = Var (weaken r i)
weakenElim r (Met m (Qruning w xs)) = Met m (Qruning (compWk w r) xs)
weakenElim r (Rgd x)         = Rgd (weaken r x)
weakenElim _ (Gbl g)         = Gbl g
weakenElim r (App i f t)     = App i (weakenElim r f) (weakenTerm r t)
weakenElim r (Sel e s)       = flip Sel s (weakenElim r e)
weakenElim r (Ann t s)       = Ann (weakenTerm r t) (weakenTerm r s)
weakenElim r (Swh e m ts)    = Swh (weakenElim r e) (weakenTerm r m) (fmap (weakenTerm r) ts)
weakenElim r (DeI d m x y z) = DeI (weakenElim r d) (weakenTerm r m) (weakenTerm r x) (weakenTerm r y) (weakenTerm r z)
weakenElim r (Let x t s)     = Let x (weakenElim r t) (weakenElim (keep r) s)
weakenElim r (Ind e m c)     = Ind (weakenElim r e) (weakenTerm r m) (weakenTerm r c)
weakenElim r (Spl e)         = Spl (weakenElim r e)
weakenElim r (WkE w e)       = weakenElim (compWk w r) e

-------------------------------------------------------------------------------
-- Contraction
-------------------------------------------------------------------------------

instance Contract (Term pass) where
    contract r (Lam x i t)   = Lam x i <$> contract (keep r) t
    contract r (Pie x i a b) = Pie x i <$> contract r a <*> contract (keep r) b
    contract r (Sgm x i a b) = Sgm x i <$> contract r a <*> contract (keep r) b
    contract r (Mul i t s)   = Mul i <$> contract r t <*> contract r s
    contract _ Uni           = pure Uni
    contract _ One           = pure One
    contract _ Tht           = pure Tht
    contract _ Dsc           = pure Dsc
    contract _ De1           = pure De1
    contract r (DeS t s)     = DeS <$> contract r t <*> contract r s
    contract r (DeX t)       = DeX <$> contract r t
    contract r (Emb e)       = Emb <$> contract r e
    contract _ (EIx i)       = pure (EIx i)
    contract _ (Fin ls)      = pure (Fin ls)
    contract r (Muu d)       = Muu <$> contract r d
    contract r (Con t)       = Con <$> contract r t
    contract r (Cod t)       = Cod <$> contract r t
    contract r (Quo t)       = Quo <$> contract r t
    contract r (WkT w t)     = contractWk w r >>= \r' -> contract r' t

instance Contract (Elim pass) where
    contract r (Var i)         = Var <$> contract r i
    contract r (Met m (Qruning w xs)) = contractWk r w <&> \w' -> Met m (Qruning w' xs)
    contract r (Rgd x)         = Rgd <$> contract r x
    contract _ (Gbl g)         = pure (Gbl g)
    contract r (App i f t)     = App i <$> contract r f <*> contract r t
    contract r (Sel e s)       = flip Sel s <$> contract r e
    contract r (Ann t s)       = Ann <$> contract r t <*> contract r s
    contract r (Swh e m ts)    = Swh <$> contract r e <*> contract r m <*> traverse (contract r) ts
    contract r (DeI d m x y z) = DeI <$> contract r d <*> contract r m <*> contract r x <*> contract r y <*> contract r z
    contract r (Let x t s)     = Let x <$> contract r t <*> contract (keep r) s
    contract r (Ind e m c)     = Ind <$> contract r e <*> contract r m <*> contract r c
    contract r (Spl e)         = Spl <$> contract r e
    contract r (WkE w e)       = contractWk w r >>= \r' -> contract r' e

contractWk :: Wk m p -> Wk n p -> Maybe (Wk n m)
contractWk IdWk w' = Just w'
contractWk (KeepWk w) IdWk        = KeepWk <$> contractWk w IdWk
contractWk (KeepWk w) (SkipWk w') = SkipWk <$> contractWk w w'
contractWk (KeepWk w) (KeepWk w') = KeepWk <$> contractWk w w'
contractWk (SkipWk _) IdWk        = Nothing
contractWk (SkipWk w) (SkipWk w') = contractWk w w'
contractWk (SkipWk _) (KeepWk _ ) = Nothing

-------------------------------------------------------------------------------
-- Var
-------------------------------------------------------------------------------

instance Var (Elim pass) where
    var = Var

instance Var (Term pass) where
    var :: Idx ctx -> Term pass ctx
    var = Emb . Var

-------------------------------------------------------------------------------
-- Renamings with Qruning
-------------------------------------------------------------------------------

qrenameTerm :: Env ctx Natural -> Term pass ctx -> Term pass ctx
qrenameTerm _  Uni     = Uni
qrenameTerm _  One     = One
qrenameTerm qr (Pie x i a b) = Pie x i (qrenameTerm qr a) (qrenameTerm (qr :> 0) b)
qrenameTerm qr (Cod a) = Cod (qrenameTerm qr a)
qrenameTerm qr (Quo a) = Quo (qrenameTerm qr a)
qrenameTerm qr (Emb e) = Emb (qrenameElim qr e)
qrenameTerm _ t = error $ "qrenameTerm: " ++ show t -- TODO

qrenameElim :: Env ctx Natural -> Elim pass ctx -> Elim pass ctx
qrenameElim qr (Var x)   = qrenameVar qr x
qrenameElim _  (Gbl g)   = Gbl g
qrenameElim _  (Met m (Qruning w EmptyEnv)) = Met m (Qruning w EmptyEnv) -- TODO: add arbitrary Qrunings
qrenameElim qr (App i f t) = App i (qrenameElim qr f) (qrenameTerm qr t)
qrenameElim qr (Spl e) = Spl (qrenameElim qr e)
qrenameElim qr (WkE w e) = WkE w (qrenameElim (weakenEnv w qr) e)
qrenameElim _ e = error $ "qrenameElim: " ++ show e -- TODO

qrenameVar :: Env ctx Natural -> Idx ctx -> Elim pass ctx
qrenameVar qr i = go (lookupEnv i qr) (Var i) where
    go NZ     e = e
    go (NS n) e = go n (spl e)

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

prettyTerm :: NameScope -> Env ctx Name -> Int -> Term pass ctx -> Doc
prettyTerm ns env d t = prettyRaw d (toRaw ns env t)

prettyElim :: NameScope -> Env ctx Name -> Int -> Elim pass ctx -> Doc
prettyElim ns env d e = prettyRaw d (toRaw ns env e)

prettyElim' :: NameScope -> Env ctx Name -> Int -> Elim pass ctx -> Doc
prettyElim' ns env d e = prettyRaw d (unRAnn (toRaw ns env e))

instance ToRaw (Term pass) where
    toRaw ns env (Lam x i t)
        = withFreshName ns x $ \ns' x' ->
          RLam x' i (toRaw ns' (env :> x') t)

    toRaw ns env (Pie x i a b)
        | Just b' <- contract unusedIdx b
        , i == Ecit
        = RArr (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RPie x' i (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (Sgm x i a b)
        | Just b' <- contract unusedIdx b
        , i == Ecit
        = RPrd (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RSgm x' i (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (Mul i t s) = RMul i (toRaw ns env t) (toRaw ns env s)
    toRaw _  _   Uni         = RUni
    toRaw _  _   One         = ROne
    toRaw _  _   Tht         = RTht
    toRaw _  _   Dsc         = RDsc
    toRaw _  _   De1         = RDe1
    toRaw ns env (DeS t s)   = RDeS (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (DeX t)     = RDeX (toRaw ns env t)
    toRaw ns env (Muu d)     = RMuu (toRaw ns env d)
    toRaw ns env (Con t)     = RCon (toRaw ns env t)
    toRaw ns env (Cod a)     = RCod (toRaw ns env a)
    toRaw ns env (Quo t)     = RQuo (toRaw ns env t)
    toRaw ns env (Emb e)     = toRaw ns env e
    toRaw _  _   (EIx i)     = REIx i
    toRaw _  _   (Fin ls)    = RFin ls
    toRaw ns env (WkT w t)   = toRaw ns (weakenEnv w env) t

instance ToRaw (Elim pass) where
    toRaw ns env (Let x t s)
        = withFreshName ns x $ \ns' x' ->
          RLet x' (toRaw ns env t) (toRaw ns' (env :> x') s)

    toRaw ns env (Swh e m ts)    = RSwh (toRaw ns env e) (toRaw ns env m) (ifoldr (\i t acc -> (Right i := toRaw ns env t) : acc) [] ts)
    toRaw _  env (Var i)         = RVar (lookupEnv i env)
    toRaw _  env (Met m xs)      = rappPruning env (RMet m) xs
    toRaw _  _   (Rgd r)         = RRgd r
    toRaw _  _   (Gbl g)         = RGbl g
    toRaw ns env (App i f t)     = rapp i (toRaw ns env f) (toRaw ns env t)
    toRaw ns env (Sel e s)       = rsel (toRaw ns env e) s
    toRaw ns env (DeI e m x y z) = RDeI (toRaw ns env e) (toRaw ns env m) (toRaw ns env x) (toRaw ns env y) (toRaw ns env z)
    toRaw ns env (Ind e m c)     = RInd (toRaw ns env e) (toRaw ns env m) (toRaw ns env c)
    toRaw ns env (Spl e)         = RSpl (toRaw ns env e)
    toRaw ns env (Ann t s)       = RAnn (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (WkE w e)       = toRaw ns (weakenEnv w env) e

rappPruning :: Env ctx Name -> Raw -> Qruning ctx -> Raw
rappPruning ns0 h0 (Qruning wk args) = go (weakenEnv wk ns0) args h0 where
    go :: Env ctx Name -> Env ctx Natural -> Raw -> Raw
    go EmptyEnv  EmptyEnv  h = h
    go (ts :> t) (qs :> q) h = rapp Ecit (go ts qs h) (quo' q (RVar t))

    quo' NZ     e = e
    quo' (NS n) e = quo' n (RQuo e)
