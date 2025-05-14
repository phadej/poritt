module PoriTT.Zonk (
    Zonk (..),
    zonkTerm,
    zonkElim,
    ZonkEnv (..),
    emptyZonkEnv,
) where

import PoriTT.Base
import PoriTT.Eval
import PoriTT.Meta
import PoriTT.Pruning
import PoriTT.Quote
import PoriTT.Term

type Zonk :: TermPass -> Type
data Zonk pass where
    FullZonk :: Zonk NoMetas
    PartZonk :: Zonk HasMetas

data ZonkEnv ctx = ZonkEnv
    { size  :: !(Size ctx)
    , metas :: !(MetaMap MetaEntry)
    }

emptyZonkEnv :: MetaMap MetaEntry -> ZonkEnv EmptyCtx
emptyZonkEnv ms = ZonkEnv SZ ms

bind :: ZonkEnv ctx -> ZonkEnv (S ctx)
bind (ZonkEnv s ms) = ZonkEnv (SS s) ms

contractEnv :: Wk ctx ctx' -> ZonkEnv ctx' -> ZonkEnv ctx
contractEnv w (ZonkEnv s ms) = ZonkEnv (contractSize w s) ms

zonkMeta :: Zonk pass -> ZonkEnv ctx -> MetaVar -> Qruning ctx -> Maybe (Elim pass ctx)
zonkMeta z env x pr = case lookupMetaMap x env.metas of
    Nothing -> Nothing -- TODO: unbound error
    Just (Solved ty t) -> case quoteElim UnfoldNone env.size (vappQruning env.size (sinkSize env.size (vann t ty)) pr) of
        Right e -> zonkElim z env e
        Left _err -> Nothing -- TODO: report error
    Just (Unsolved _) -> case z of
        FullZonk -> Nothing -- unsolved meta
        PartZonk -> Just (Met x pr)

zonkTerm :: Zonk pass -> ZonkEnv ctx -> Term pass' ctx -> Maybe (Term pass ctx)
-- we handle zonk of embedded meta specially, to avoid extra type annotations
zonkTerm z env (Emb (Met x pr)) = emb <$> zonkMeta z env x pr
zonkTerm z env (Emb e)       = Emb <$> zonkElim z env e
zonkTerm _ _   Uni           = pure Uni
zonkTerm _ _   One           = pure One
zonkTerm _ _   Dsc           = pure Dsc
zonkTerm _ _   De1           = pure De1
zonkTerm _ _   Tht           = pure Tht
zonkTerm z env (DeX t)       = DeX <$> zonkTerm z env t
zonkTerm z env (DeS t r)     = DeS <$> zonkTerm z env t <*> zonkTerm z env r
zonkTerm z env (Con t)       = Con <$> zonkTerm z env t
zonkTerm z env (Muu t)       = Muu <$> zonkTerm z env t
zonkTerm _ _   (EIx i)       = pure (EIx i)
zonkTerm z env (Pie x i a b) = Pie x i <$> zonkTerm z env a <*> zonkTerm z (bind env) b
zonkTerm z env (Sgm x i a b) = Sgm x i <$> zonkTerm z env a <*> zonkTerm z (bind env) b
zonkTerm _ _   (Fin ls)      = pure (Fin ls)
zonkTerm z env (Mul i t r)   = Mul i <$> zonkTerm z env t <*> zonkTerm z env r
zonkTerm z env (Lam x i t)   = Lam x i <$> zonkTerm z (bind env) t
zonkTerm z env (Cod t)       = Cod <$> zonkTerm z env t
zonkTerm z env (Quo t)       = Quo <$> zonkTerm z env t
zonkTerm z env (WkT w t)     = WkT w <$> zonkTerm z (contractEnv w env) t

zonkElim :: Zonk pass -> ZonkEnv ctx -> Elim pass' ctx -> Maybe (Elim pass ctx)
zonkElim z env (Met x pr)      = zonkMeta z env x pr
zonkElim _ _   (Rgd _)         = Nothing
zonkElim _ _   (Var x)         = pure (Var x)
zonkElim _ _   (Gbl g)         = pure (Gbl g)
zonkElim z env (App i f t)     = App i <$> zonkElim z env f <*> zonkTerm z env t
zonkElim z env (Sel e f)       = Sel <$> zonkElim z env e <*> pure f
zonkElim z env (Swh e p ts)    = Swh <$> zonkElim z env e <*> zonkTerm z env p <*> traverse (zonkTerm z env) ts
zonkElim z env (Ind e x y)     = Ind <$> zonkElim z env e <*> zonkTerm z env x <*> zonkTerm z env y
zonkElim z env (DeI e p x y w) = DeI <$> zonkElim z env e <*> zonkTerm z env p <*> zonkTerm z env x <*> zonkTerm z env y <*> zonkTerm z env w
zonkElim z env (Spl e)         = Spl <$> zonkElim z env e
zonkElim z env (Ann t a)       = Ann <$> zonkTerm z env t <*> zonkTerm z env a
zonkElim z env (Let x t r)     = Let x <$> zonkElim z env t <*> zonkElim z (bind env) r
zonkElim z env (WkE w e)       = WkE w <$> zonkElim z (contractEnv w env) e
