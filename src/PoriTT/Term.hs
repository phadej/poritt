module PoriTT.Term (
    TermPass (..),
    Term (..),
    Elim (..),
    prettyTerm,
    prettyElim,
    prettyElim',
    emb,
    ann,
    coeNoMetasElim,
    coeSizeElim,
) where

import Unsafe.Coerce (unsafeCoerce)

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Icit
import PoriTT.Meta.Var
import PoriTT.Name
import PoriTT.PP
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
    Met :: MetaVar -> Elim HasMetas ctx
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

-------------------------------------------------------------------------------
-- Renaming
-------------------------------------------------------------------------------

instance Renamable (Term pass) where
    rename = defaultRename

    -- we have explicit weakening in the terms.
    -- it doesn't complicate evaluation nor linting,
    -- in these cases we don't end up traversing terms extra times.
    weaken w (WkT w' t) = WkT (compWk w' w) t
    weaken w t          = WkT w t

instance Renamable (Elim pass) where
    rename = defaultRename
    weaken w (WkE w' e) = WkE (compWk w' w) e
    weaken w (Var i)    = Var (weakenIdx w i)
    weaken _ (Met m)    = Met m
    weaken _ (Gbl g)    = Gbl g
    weaken w e          = WkE w e

instance RenamableA (Term pass) where
    grename r (Lam x i t)   = Lam x i <$> grename (keep r) t
    grename r (Pie x i a b) = Pie x i <$> grename r a <*> grename (keep r) b
    grename r (Sgm x i a b) = Sgm x i <$> grename r a <*> grename (keep r) b
    grename r (Mul i t s)   = Mul i <$> grename r t <*> grename r s
    grename _ Uni           = pure Uni
    grename _ One           = pure One
    grename _ Tht           = pure Tht
    grename _ Dsc           = pure Dsc
    grename _ De1           = pure De1
    grename r (DeS t s)     = DeS <$> grename r t <*> grename r s
    grename r (DeX t)       = DeX <$> grename r t
    grename r (Emb e)       = Emb <$> grename r e
    grename _ (EIx i)       = pure (EIx i)
    grename _ (Fin ls)      = pure (Fin ls)
    grename r (Muu d)       = Muu <$> grename r d
    grename r (Con t)       = Con <$> grename r t
    grename r (Cod t)       = Cod <$> grename r t
    grename r (Quo t)       = Quo <$> grename r t
    grename r (WkT w t)     = grename (weakenIdxMapping w r) t

instance RenamableA (Elim pass) where
    grename r (Var i)         = Var <$> grename r i
    grename _ (Met m)         = pure (Met m)
    grename r (Rgd x)         = Rgd <$> grename r x
    grename _ (Gbl g)         = pure (Gbl g)
    grename r (App i f t)     = App i <$> grename r f <*> grename r t
    grename r (Sel e s)       = flip Sel s <$> grename r e
    grename r (Ann t s)       = Ann <$> grename r t <*> grename r s
    grename r (Swh e m ts)    = Swh <$> grename r e <*> grename r m <*> traverse (grename r) ts
    grename r (DeI d m x y z) = DeI <$> grename r d <*> grename r m <*> grename r x <*> grename r y <*> grename r z
    grename r (Let x t s)     = Let x <$> grename r t <*> grename (keep r) s
    grename r (Ind e m c)     = Ind <$> grename r e <*> grename r m <*> grename r c
    grename r (Spl e)         = Spl <$> grename r e
    grename r (WkE w e)       = grename (weakenIdxMapping w r) e

-------------------------------------------------------------------------------
-- Var
-------------------------------------------------------------------------------

instance Var (Elim pass) where
    var = Var

instance Var (Term pass) where
    var = Emb . Var

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
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
        , i == Ecit
        = RArr (toRaw ns env a) (toRaw ns env b')

        | otherwise
        = withFreshName ns x $ \ns' x' ->
          RPie x' i (toRaw ns env a) (toRaw ns' (env :> x') b)

    toRaw ns env (Sgm x i a b)
        | Just b' <- renameA (unusedIdx (sizeEnv env)) b
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
    toRaw _  _   (Met m)         = RMet m
    toRaw _  _   (Rgd r)         = RRgd r
    toRaw _  _   (Gbl g)         = RGbl g
    toRaw ns env (App i f t)     = rapp i (toRaw ns env f) (toRaw ns env t)
    toRaw ns env (Sel e s)       = rsel (toRaw ns env e) s
    toRaw ns env (DeI e m x y z) = RDeI (toRaw ns env e) (toRaw ns env m) (toRaw ns env x) (toRaw ns env y) (toRaw ns env z)
    toRaw ns env (Ind e m c)     = RInd (toRaw ns env e) (toRaw ns env m) (toRaw ns env c)
    toRaw ns env (Spl e)         = RSpl (toRaw ns env e)
    toRaw ns env (Ann t s)       = RAnn (toRaw ns env t) (toRaw ns env s)
    toRaw ns env (WkE w e)       = toRaw ns (weakenEnv w env) e
