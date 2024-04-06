module PoriTT.Zonk (
    zonkTerm,
    zonkElim,
    ZonkEnv (..),
    emptyZonkEnv,
) where

import PoriTT.Base
import PoriTT.Term
import PoriTT.Meta
import PoriTT.Eval
import PoriTT.Quote

data ZonkEnv ctx = ZonkEnv
    { size  :: !(Size ctx)
    , metas :: !(MetaMap MetaEntry)
    }

emptyZonkEnv :: MetaMap MetaEntry -> ZonkEnv EmptyCtx
emptyZonkEnv ms = ZonkEnv SZ ms

bind :: ZonkEnv ctx -> ZonkEnv (S ctx)
bind (ZonkEnv s ms) = ZonkEnv (SS s) ms

contract :: Wk ctx ctx' -> ZonkEnv ctx' -> ZonkEnv ctx
contract w (ZonkEnv s ms) = ZonkEnv (contractSize w s) ms

zonkTerm :: ZonkEnv ctx -> Term pass ctx -> Maybe (Term NoMetas ctx)
zonkTerm env (Emb (Met x pr)) = case lookupMetaMap x env.metas of
    Just (Solved ty t) -> case quoteElim UnfoldNone env.size (vappPruning env.size (sinkSize env.size (vann t ty)) pr) of
        Right e -> zonkTerm env (emb e)
        Left err -> Nothing -- TODO
    _ -> Nothing

zonkTerm env (Emb e)       = Emb <$> zonkElim env e
zonkTerm _   Uni           = pure Uni
zonkTerm _   One           = pure One
zonkTerm _   Dsc           = pure Dsc
zonkTerm _   De1           = pure De1
zonkTerm _   Tht           = pure Tht
zonkTerm env (DeX t)       = DeX <$> zonkTerm env t
zonkTerm env (DeS t r)     = DeS <$> zonkTerm env t <*> zonkTerm env r
zonkTerm env (Con t)       = Con <$> zonkTerm env t
zonkTerm env (Muu t)       = Muu <$> zonkTerm env t
zonkTerm _   (EIx i)       = pure (EIx i)
zonkTerm env (Pie x i a b) = Pie x i <$> zonkTerm env a <*> zonkTerm (bind env) b
zonkTerm env (Sgm x i a b) = Sgm x i <$> zonkTerm env a <*> zonkTerm (bind env) b
zonkTerm _   (Fin ls)      = pure (Fin ls)
zonkTerm env (Mul i t r)   = Mul i <$> zonkTerm env t <*> zonkTerm env r
zonkTerm env (Lam x i t)   = Lam x i <$> zonkTerm (bind env) t
zonkTerm env (Cod t)       = Cod <$> zonkTerm env t
zonkTerm env (Quo t)       = Quo <$> zonkTerm env t
zonkTerm env (WkT w t)     = WkT w <$> zonkTerm (contract w env) t

zonkElim :: ZonkEnv ctx -> Elim pass ctx -> Maybe (Elim NoMetas ctx)
zonkElim env (Met x pr)      = case lookupMetaMap x env.metas of
    Just (Solved ty t) -> case quoteElim UnfoldNone env.size (vappPruning env.size (sinkSize env.size (vann t ty)) pr) of
        Right e -> zonkElim env e
        Left err -> Nothing -- TODO
    _ -> Nothing
zonkElim _   (Rgd _)         = Nothing
zonkElim _   (Var x)         = pure (Var x)
zonkElim _   (Gbl g)         = pure (Gbl g)
zonkElim env (App i f t)     = App i <$> zonkElim env f <*> zonkTerm env t
zonkElim env (Sel e f)       = Sel <$> zonkElim env e <*> pure f
zonkElim env (Swh e p ts)    = Swh <$> zonkElim env e <*> zonkTerm env p <*> traverse (zonkTerm env) ts
zonkElim env (Ind e x y)     = Ind <$> zonkElim env e <*> zonkTerm env x <*> zonkTerm env y
zonkElim env (DeI e p x y z) = DeI <$> zonkElim env e <*> zonkTerm env p <*> zonkTerm env x <*> zonkTerm env y <*> zonkTerm env z
zonkElim env (Spl e)         = Spl <$> zonkElim env e
zonkElim env (Ann t a)       = Ann <$> zonkTerm env t <*> zonkTerm env a
zonkElim env (Let x t r)     = Let x <$> zonkElim env t <*> zonkElim (bind env) r
zonkElim env (WkE w e)       = WkE w <$> zonkElim (contract w env) e
