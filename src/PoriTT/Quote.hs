-- | Quote from values ('VTerm' and 'VElim') to terms ('Term' and 'Elim').
--
-- We could quote to normal forms too (see "PoriTT.Norm"),
-- but in practice it's more convenient to quote into terms.
module PoriTT.Quote (
    quoteTerm,
    quoteElim,
    Unfold (..),
    prettyVElim,
    prettyVTerm,
    nfTerm,
    nfElim,
    preElim,
    preTerm,
) where

import PoriTT.Base
import PoriTT.Eval
import PoriTT.Name
import PoriTT.PP
import PoriTT.Term
import PoriTT.Value

-------------------------------------------------------------------------------
-- Quoting
-------------------------------------------------------------------------------

-- | How much to unfold when quoting?
data Unfold
    = UnfoldNone  -- ^ unfold nothing
    | UnfoldElim  -- ^ don't unfold spines of neutral elements
    | UnfoldAll   -- ^ unfold all
  deriving Show

-- | Quote semantic value into normal form.
--
-- Quoting will force the evaluation errors.
--
quoteTerm
    :: Unfold -- ^ Unfold global definitions
    -> Size ctx -> VTerm pass ctx -> Either EvalError (Term pass ctx)
quoteTerm u s (VLam x i clos) = Lam x i <$> quoteTerm u (SS s) (runZ s clos)
quoteTerm u s (VPie x i a b)  = Pie x i <$> quoteTerm u s a <*> quoteTerm u (SS s) (runZ s b)
quoteTerm u s (VSgm x i a b)  = Sgm x i <$> quoteTerm u s a <*> quoteTerm u (SS s) (runZ s b)
quoteTerm u s (VMul i t r)    = Mul i <$> quoteTerm u s t <*> quoteTerm u s r
quoteTerm u s (VDeS t r)      = DeS <$> quoteTerm u s t <*> quoteTerm u s r
quoteTerm u s (VDeX t)        = DeX <$> quoteTerm u s t
quoteTerm u s (VMuu t)        = Muu <$> quoteTerm u s t
quoteTerm u s (VCon t)        = Con <$> quoteTerm u s t
quoteTerm _ _ VUni            = pure Uni
quoteTerm _ _ VOne            = pure One
quoteTerm _ _ VTht            = pure Tht
quoteTerm _ _ VDsc            = pure Dsc
quoteTerm _ _ VDe1            = pure De1
quoteTerm _ _ (VEIx i)        = pure (EIx i)
quoteTerm _ _ (VFin ls)       = pure (Fin ls)
quoteTerm u s (VCod t)        = Cod <$> quoteTerm u s t
quoteTerm _ s (VQuo t _)      = Quo <$> quoteSTerm NZ s t
quoteTerm u s (VEmb e)        = emb <$> quoteElim u s e

quoteElim :: Unfold -> Size ctx -> VElim pass ctx -> Either EvalError (Elim pass ctx)
quoteElim u s (VRgd l sp)   = quoteSpine (unfoldSp u) s (pure (Var (lvlToIdx s l))) sp
quoteElim u s (VFlx m sp)   = quoteSpine (unfoldSp u) s (pure (Met m)) sp
quoteElim u s (VGbl g sp t) = case u of
    UnfoldAll  -> quoteElim u s t
    UnfoldElim -> quoteElim u s t
    UnfoldNone -> quoteSpine u s (pure (Gbl g)) sp
quoteElim u s (VAnn t a)    = ann <$> quoteTerm u s t <*> quoteTerm u s a
quoteElim _ _ (VErr msg)    = Left msg

unfoldSp :: Unfold -> Unfold
unfoldSp UnfoldElim = UnfoldNone
unfoldSp u          = u

quoteSpine :: Unfold -> Size ctx -> Either EvalError (Elim pass ctx) -> Spine pass ctx -> Either EvalError (Elim pass ctx)
quoteSpine _ _ h VNil              = h
quoteSpine u s h (VApp sp i e)     = App i <$> quoteSpine u s h sp <*> quoteTerm u s e
quoteSpine u s h (VSel sp z)       = Sel <$> quoteSpine u s h sp <*> pure z
quoteSpine u s h (VSwh sp m ts)    = Swh <$> quoteSpine u s h sp <*> quoteTerm u s m <*> traverse (quoteTerm u s) ts
quoteSpine u s h (VDeI sp m x y z) = DeI <$> quoteSpine u s h sp <*> quoteTerm u s m <*> quoteTerm u s x <*> quoteTerm u s y <*> quoteTerm u s z
quoteSpine u s h (VInd sp m t)     = Ind <$> quoteSpine u s h sp <*> quoteTerm u s m <*> quoteTerm u s t
quoteSpine u s h (VSpl sp)         = Spl <$> quoteSpine u s h sp

-------------------------------------------------------------------------------
-- Quoting of STerm and SElim
-------------------------------------------------------------------------------

quoteSTerm :: Natural -> Size ctx -> STerm pass ctx -> Either EvalError (Term pass ctx)
quoteSTerm l      s (SLam n i clos) = Lam n i <$> quoteSTerm l (SS s) (runSTZ s clos)
quoteSTerm l      s (SPie x i a b)  = Pie x i <$> quoteSTerm l s a <*> quoteSTerm l (SS s) (runSTZ s b)
quoteSTerm l      s (SSgm x i a b)  = Sgm x i <$> quoteSTerm l s a <*> quoteSTerm l (SS s) (runSTZ s b)
quoteSTerm l      s (SMul i t r)    = Mul i <$> quoteSTerm l s t <*> quoteSTerm l s r
quoteSTerm _      _ SUni            = pure Uni
quoteSTerm _      _ SOne            = pure One
quoteSTerm _      _ STht            = pure Tht
quoteSTerm _      _ SDsc            = pure Dsc
quoteSTerm _      _ SDe1            = pure De1
quoteSTerm l      s (SDeS t r)      = DeS <$> quoteSTerm l s t <*> quoteSTerm l s r
quoteSTerm l      s (SDeX t)        = DeX <$> quoteSTerm l s t
quoteSTerm _      _ (SEIx i)        = pure (EIx i)
quoteSTerm _      _ (SFin ls)       = pure (Fin ls)
quoteSTerm l      s (SMuu t)        = Muu <$> quoteSTerm l s t
quoteSTerm l      s (SCon t)        = Con <$> quoteSTerm l s t
quoteSTerm l      s (SCod t)        = Cod <$> quoteSTerm l s t
quoteSTerm l      s (SQuo t)        = Quo <$> quoteSTerm (NS l) s t
quoteSTerm l      s (SEmb e)        = Emb <$> quoteSElim l s e

quoteSElim :: Natural -> Size ctx -> SElim pass ctx -> Either EvalError (Elim pass ctx)
quoteSElim _      s (SVar x)         = pure $ Var (lvlToIdx s x)
quoteSElim _      _ (SGbl g)         = pure $ Gbl g
quoteSElim l      s (SApp i f t)     = App i <$> quoteSElim l s f <*> quoteSTerm l s t
quoteSElim l      s (SSel e t)       = Sel <$> quoteSElim l s e <*> pure t
quoteSElim l      s (SSwh e m ts)    = Swh <$> quoteSElim l s e <*> quoteSTerm l s m <*> traverse (quoteSTerm l s) ts
quoteSElim l      s (SInd e m t)     = Ind <$> quoteSElim l s e <*> quoteSTerm l s m <*> quoteSTerm l s t
quoteSElim l      s (SDeI e m x y z) = DeI <$> quoteSElim l s e <*> quoteSTerm l s m <*> quoteSTerm l s x <*> quoteSTerm l s y <*> quoteSTerm l s z
quoteSElim l      s (SAnn t a)       = Ann <$> quoteSTerm l s t <*> quoteSTerm l s a
quoteSElim (NS l) s (SSpl e _)       = Spl <$> quoteSElim l s e
quoteSElim NZ     s (SSpl _ e)       = quoteElim UnfoldNone s e
quoteSElim l      s (SLet x e f)     = Let x <$> quoteSElim l s e <*> quoteSElim l (SS s) (runSEZ s f)
quoteSElim _      _ (SErr msg)       = Left msg

-------------------------------------------------------------------------------
-- Normalisation
-------------------------------------------------------------------------------

nfTerm :: Unfold  -> Size ctx' -> EvalEnv pass ctx ctx' -> Term pass ctx -> Either EvalError (Term pass ctx')
nfTerm u s ee t = quoteTerm u s (evalTerm s ee t)

nfElim :: Unfold  -> Size ctx' -> EvalEnv pass ctx ctx' -> Elim pass ctx -> Either EvalError (Elim pass ctx')
nfElim u s ee t = quoteElim u s (evalElim s ee t)

-------------------------------------------------------------------------------
-- Staging
-------------------------------------------------------------------------------

preElim :: Size ctx' -> EvalEnv pass ctx ctx' -> Elim pass ctx -> Either EvalError (Elim pass ctx')
preElim s env e = quoteSElim NZ s $ stageElim s env e

preTerm :: Size ctx' -> EvalEnv pass ctx ctx' -> Term pass ctx -> Either EvalError (Term pass ctx')
preTerm s env t = quoteSTerm NZ s $ stageTerm s env t

-------------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------------

prettyVTerm :: Size ctx -> NameScope -> Env ctx Name -> VTerm pass ctx -> Doc
prettyVTerm s ns env v = case quoteTerm UnfoldNone s v of
    Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
    Right n  -> prettyTerm ns env 0 n

prettyVElim :: Size ctx -> NameScope -> Env ctx Name -> VElim pass ctx -> Doc
prettyVElim s ns env v = case quoteElim UnfoldNone s v of
    Left err -> ppStr (show err) -- This shouldn't happen if type-checker is correct.
    Right e  -> prettyElim ns env 0 e
