module PoriTT.Zonk (
    zonkTerm,
    zonkElim,
) where

import PoriTT.Base
import PoriTT.Term

zonkTerm :: Term pass ctx -> Maybe (Term NoMetas ctx)
zonkTerm (Emb e)       = Emb <$> zonkElim e
zonkTerm Uni           = pure Uni
zonkTerm One           = pure One
zonkTerm Dsc           = pure Dsc
zonkTerm De1           = pure De1
zonkTerm Tht           = pure Tht
zonkTerm (DeX t)       = DeX <$> zonkTerm t
zonkTerm (DeS t s)     = DeS <$> zonkTerm t <*> zonkTerm s
zonkTerm (Con t)       = Con <$> zonkTerm t
zonkTerm (Muu t)       = Muu <$> zonkTerm t
zonkTerm (EIx i)       = pure (EIx i)
zonkTerm (Pie x i a b) = Pie x i <$> zonkTerm a <*> zonkTerm b
zonkTerm (Sgm x i a b) = Sgm x i <$> zonkTerm a <*> zonkTerm b
zonkTerm (Fin ls)      = pure (Fin ls)
zonkTerm (Mul i t s)   = Mul i <$> zonkTerm t <*> zonkTerm s
zonkTerm (Lam x i t)   = Lam x i <$> zonkTerm t
zonkTerm (Cod t)       = Cod <$> zonkTerm t
zonkTerm (Quo t)       = Quo <$> zonkTerm t
zonkTerm (WkT w t)     = WkT w <$> zonkTerm t

zonkElim :: Elim pass ctx -> Maybe (Elim NoMetas ctx)
zonkElim (Met _)         = TODO
zonkElim (Rgd _)         = Nothing
zonkElim (Var x)         = pure (Var x)
zonkElim (Gbl g)         = pure (Gbl g)
zonkElim (App i f t)     = App i <$> zonkElim f <*> zonkTerm t
zonkElim (Sel e s)       = Sel <$> zonkElim e <*> pure s
zonkElim (Swh e m ts)    = Swh <$> zonkElim e <*> zonkTerm m <*> traverse zonkTerm ts
zonkElim (Ind e x y)     = Ind <$> zonkElim e <*> zonkTerm x <*> zonkTerm y
zonkElim (DeI e m x y z) = DeI <$> zonkElim e <*> zonkTerm m <*> zonkTerm x <*> zonkTerm y <*> zonkTerm z
zonkElim (Spl e)         = Spl <$> zonkElim e
zonkElim (Ann t a)       = Ann <$> zonkTerm t <*> zonkTerm a
zonkElim (Let x t s)     = Let x <$> zonkElim t <*> zonkElim s
zonkElim (WkE w e)       = WkE w <$> zonkElim e
