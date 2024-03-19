module PoriTT.Zonk (
    zonkTerm,
    zonkElim,
) where

import PoriTT.Base
import PoriTT.Term
import PoriTT.Meta

zonkTerm :: Size ctx -> MetaMap MetaEntry -> Term pass ctx -> Maybe (Term NoMetas ctx)
zonkTerm s m (Emb e)       = Emb <$> zonkElim s m e
zonkTerm s m Uni           = pure Uni
zonkTerm s m One           = pure One
zonkTerm s m Dsc           = pure Dsc
zonkTerm s m De1           = pure De1
zonkTerm s m Tht           = pure Tht
zonkTerm s m (DeX t)       = DeX <$> zonkTerm s m t
zonkTerm s m (DeS t r)     = DeS <$> zonkTerm s m t <*> zonkTerm s m r
zonkTerm s m (Con t)       = Con <$> zonkTerm s m t
zonkTerm s m (Muu t)       = Muu <$> zonkTerm s m t
zonkTerm s m (EIx i)       = pure (EIx i)
zonkTerm s m (Pie x i a b) = Pie x i <$> zonkTerm s m a <*> zonkTerm (SS s) m b
zonkTerm s m (Sgm x i a b) = Sgm x i <$> zonkTerm s m a <*> zonkTerm (SS s) m b
zonkTerm s m (Fin ls)      = pure (Fin ls)
zonkTerm s m (Mul i t r)   = Mul i <$> zonkTerm s m t <*> zonkTerm s m r
zonkTerm s m (Lam x i t)   = Lam x i <$> zonkTerm (SS s) m t
zonkTerm s m (Cod t)       = Cod <$> zonkTerm s m t
zonkTerm s m (Quo t)       = Quo <$> zonkTerm s m t
zonkTerm s m (WkT w t)     = WkT w <$> zonkTerm (contractSize w s) m t

zonkElim :: Size ctx -> MetaMap MetaEntry -> Elim pass ctx -> Maybe (Elim NoMetas ctx)
zonkElim s m (Met x)         = case lookupMetaMap x m of
    Just (Solved ty _ t _) -> coeSizeElim <$> zonkElim SZ m (ann t ty)
    _ -> Nothing
zonkElim s m (Rgd _)         = Nothing
zonkElim s m (Var x)         = pure (Var x)
zonkElim s m (Gbl g)         = pure (Gbl g)
zonkElim s m (App i f t)     = App i <$> zonkElim s m f <*> zonkTerm s m t
zonkElim s m (Sel e f)       = Sel <$> zonkElim s m e <*> pure f
zonkElim s m (Swh e p ts)    = Swh <$> zonkElim s m e <*> zonkTerm s m p <*> traverse (zonkTerm s m) ts
zonkElim s m (Ind e x y)     = Ind <$> zonkElim s m e <*> zonkTerm s m x <*> zonkTerm s m y
zonkElim s m (DeI e p x y z) = DeI <$> zonkElim s m e <*> zonkTerm s m p <*> zonkTerm s m x <*> zonkTerm s m y <*> zonkTerm s m z
zonkElim s m (Spl e)         = Spl <$> zonkElim s m e
zonkElim s m (Ann t a)       = Ann <$> zonkTerm s m t <*> zonkTerm s m a
zonkElim s m (Let x t r)     = Let x <$> zonkElim s m t <*> zonkElim (SS s) m r
zonkElim s m (WkE w e)       = WkE w <$> zonkElim (contractSize w s) m e
