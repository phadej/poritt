module PoriTT.Simpl (
    SimplCtx,
    emptySimplCtx,
    SimplOpts (..),
    simplTerm,
    simplElim,
) where

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Global
import PoriTT.Nice
import PoriTT.Stage
import PoriTT.Term

data SimplOpts = SimplOpts
    { iters :: Int
    }
  deriving Show

-- TODO: why not pass ctx ctx' ?
data SimplCtx pass ctx = SimplCtx
    { sub    :: Sub (Elim pass) ctx ctx
    , size   :: Size ctx
    , cstage :: Stage
    , opts   :: SimplOpts
    }

emptySimplCtx :: SimplOpts -> SimplCtx pass EmptyCtx
emptySimplCtx opts = SimplCtx
    { sub    = emptySub
    , size   = SZ
    , cstage = stage0
    , opts   = opts
    }

bindSimplCtx :: SimplCtx pass ctx -> Elim pass ctx -> SimplCtx pass (S ctx)
bindSimplCtx ctx e = SimplCtx
    { sub    = MkSub $ fmap (weaken wk1) $ unSub $ snocSub ctx.sub e
    , size   = SS ctx.size
    , cstage = ctx.cstage
    , opts   = ctx.opts
    }

keepSimplCtx :: SimplCtx pass ctx -> SimplCtx pass (S ctx)
keepSimplCtx ctx = SimplCtx
    { sub    = keepSub ctx.sub
    , size   = SS ctx.size
    , cstage = ctx.cstage
    , opts   = ctx.opts
    }

simplTerm :: SimplCtx pass ctx -> Term pass ctx -> Term pass ctx
simplTerm ctx (WkT w t)     = simplTerm ctx (weakenTerm w t) -- TODO: weakenEnv
simplTerm ctx (Lam n i t)   = Lam n i (simplTerm (keepSimplCtx ctx) t)
simplTerm ctx (Pie n i a b) = Pie n i (simplTerm ctx a) (simplTerm (keepSimplCtx ctx) b)
simplTerm ctx (Sgm n i a b) = Sgm n i (simplTerm ctx a) (simplTerm (keepSimplCtx ctx) b)
simplTerm ctx (Mul i t s)   = Mul i (simplTerm ctx t) (simplTerm ctx s)
simplTerm _   (EIx i)       = EIx i
simplTerm _   (Fin ls)      = Fin ls
simplTerm _   Uni           = Uni
simplTerm _   One           = One
simplTerm _   Tht           = Tht
simplTerm _   Dsc           = Dsc
simplTerm _   De1           = De1
simplTerm ctx (DeS s t)     = DeS (simplTerm ctx s) (simplTerm ctx t)
simplTerm ctx (DeX t)       = DeX (simplTerm ctx t)
simplTerm ctx (Muu t)       = Muu (simplTerm ctx t)
simplTerm ctx (Con t)       = Con (simplTerm ctx t)
simplTerm ctx (Cod a)       = Cod (simplTerm ctx a)
simplTerm ctx (Quo t)       = Quo (simplTerm ctx { cstage = succ ctx.cstage } t)
simplTerm ctx (Emb e)
    | ctx.cstage == stage0
    , Ann t _ <- e
    = simplTerm ctx t

    | otherwise
    = emb (simplElim ctx e)

simplElim :: SimplCtx pass ctx -> Elim pass ctx -> Elim pass ctx
simplElim ctx (WkE w e) = simplElim ctx (weakenElim w e)
simplElim ctx (Var i)
    = substIdx ctx.sub i -- TODO: this is broken

simplElim _ (Met m xs)
    = Met m xs

simplElim _ (Rgd r)
    = Rgd r

simplElim ctx (Gbl g)
    | g.inline
    , ctx.cstage == stage0
    = coeNoMetasElim (weakenUsingSize ctx.size g.term)

    | otherwise
    = Gbl g

simplElim ctx (Let n t s)
    -- unused binding
    | ctx.cstage == stage0
    , Just s' <- contract unusedIdx s
    = simplElim ctx s'

    -- inline small terms
    | ctx.cstage == stage0
    , shouldInline t'
    = Let n t' (simplElim (bindSimplCtx ctx t') s)

    | otherwise
    = Let n t' (simplElim (keepSimplCtx ctx) s)
  where
    t' = simplElim ctx t

simplElim ctx (App i f s)
    | ctx.cstage == stage0
    , Ann (Lam x _j t) (Pie _x _k a b) <- f'
    = simplElim ctx $ Let x (Ann s a) (Ann t b)

    | otherwise
    = App i f' (simplTerm ctx s)
 where
    f' = simplElim ctx f

simplElim ctx (Sel e z)
    | ctx.cstage == stage0
    , Ann (Mul _i t _) (Sgm _ _j a _) <- e'
    , "fst" <- z
    = simplElim ctx (Ann t a)

    | ctx.cstage == stage0
    , Ann (Mul _i t r) (Sgm x _j a b) <- e'
    , "snd" <- z
    = simplElim ctx
        $ Let x (Ann t a) (Ann (weaken wk1 r) b)

    | otherwise
    = Sel e' z
  where
    e' = simplElim ctx e

simplElim ctx (Swh e m ts)
    | ctx.cstage == stage0
    , Ann (EIx i) (Fin ls) <- e'
    , Just t <- lookupEnumList i ts
    = Ann (simplTerm ctx t) (simplTerm ctx $ Emb $ Ann m (Fin ls ~~> Uni) @@ EIx i)

    | otherwise
    = Swh e' (simplTerm ctx m) (fmap (simplTerm ctx) ts)
  where
    e' = simplElim ctx e

simplElim ctx (DeI e m x y z)
    -- can and should we optimize here?
    -- at least when e is Ann De1 Dsc?
    | otherwise
    = DeI (simplElim ctx e) (simplTerm ctx m) (simplTerm ctx x) (simplTerm ctx y) (simplTerm ctx z)

simplElim ctx (Ind e m t)
    -- can and should we optimize here?
    | otherwise
    = Ind (simplElim ctx e) (simplTerm ctx m) (simplTerm ctx t)

simplElim ctx (Ann (Emb e) _)
    = simplElim ctx e

simplElim ctx (Ann t s)
    | otherwise
    = Ann (simplTerm ctx t) (simplTerm ctx s)

simplElim ctx (Spl e)
    | otherwise
    = spl (simplElim ctx { cstage = pred ctx.cstage } e)

shouldInline :: Elim pass ctx -> Bool
shouldInline (Var _)         = True
shouldInline (Gbl _)         = True
shouldInline (Ann De1 _)     = True
shouldInline (Ann (EIx _) _) = True
shouldInline (Ann Uni _)     = True
shouldInline (Ann Dsc _)     = True
shouldInline _               = False
