-- | Partial renaming
module PoriTT.PRen (
    PRen,
    PRenEnv (..),
    prenTerm,
) where

import PoriTT.Base
import PoriTT.Eval
import PoriTT.LvlMap
import PoriTT.Meta
import PoriTT.Name
import PoriTT.PP
import PoriTT.Term
import PoriTT.Value

-- | Partial renaming
--
-- Implemented with 'Lvl's, as these can be sunk for free.
type PRen ctx ctx' = LvlMap ctx (Lvl ctx')

liftPRen :: Size ctx -> Size ctx' -> PRen ctx ctx' -> PRen (S ctx) (S ctx')
liftPRen s s' p = insertLvlMap (lvlZ s) (lvlZ s') (mapSink (sinkLvlMap p))

data PRenEnv ctx ctx' = PRenEnv
    { size  :: Size ctx
    , size' :: Size ctx'
    , pren  :: PRen ctx ctx'
    , meta  :: MetaVar
    -- TODO: add names
    }

bind :: Name -> PRenEnv ctx ctx' -> PRenEnv (S ctx) (S ctx')
bind _ (PRenEnv s s' p m) = PRenEnv (SS s) (SS s') (liftPRen s s' p) m

prenTerm :: PRenEnv ctx ctx' -> VTerm HasMetas ctx -> Either Doc (Term HasMetas ctx')
prenTerm env (VLam x i clos) = Lam x i <$> prenTerm (bind x env) (runZ env.size clos)
prenTerm env (VPie x i a b)  = Pie x i <$> prenTerm env a <*> prenTerm (bind x env) (runZ env.size b)
prenTerm env (VSgm x i a b)  = Sgm x i <$> prenTerm env a <*> prenTerm (bind x env) (runZ env.size b)
prenTerm env (VMul i t r)    = Mul i <$> prenTerm env t <*> prenTerm env r
prenTerm env (VDeS t r)      = DeS <$> prenTerm env t <*> prenTerm env r
prenTerm env (VDeX t)        = DeX <$> prenTerm env t
prenTerm env (VMuu t)        = Muu <$> prenTerm env t
prenTerm env (VCon t)        = Con <$> prenTerm env t
prenTerm _   VUni            = pure Uni
prenTerm _   VOne            = pure One
prenTerm _   VTht            = pure Tht
prenTerm _   VDsc            = pure Dsc
prenTerm _   VDe1            = pure De1
prenTerm _   (VEIx i)        = pure (EIx i)
prenTerm _   (VFin ls)       = pure (Fin ls)
prenTerm env (VCod t)        = Cod <$> prenTerm env t
prenTerm env (VQuo t _)      = Quo <$> prenSTerm env NZ t
prenTerm env (VEmb e)        = emb <$> prenElim env e

prenElim :: PRenEnv ctx ctx' -> VElim HasMetas ctx -> Either Doc (Elim HasMetas ctx')
prenElim env (VRgd l sp) = case lookupLvlMap l env.pren of
    Nothing -> throwError "scope error, escaping variable"
    Just l' -> prenSpine env (Var (lvlToIdx env.size' l')) sp

prenElim _ e = error (show e)

prenSpine :: PRenEnv ctx ctx' -> Elim HasMetas ctx' -> Spine HasMetas ctx -> Either Doc (Elim HasMetas ctx')
prenSpine _   h VNil         = pure h
prenSpine env h (VApp sp i t) = App i <$> prenSpine env h sp <*> prenTerm env t

prenSpine _env _ _ = throwError "cannot rename spine" -- TODO

prenSTerm :: TODO
prenSTerm = prenSTerm


{-

-- perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []        = pure t
  goSp pren t (sp :> u) = App <$> goSp pren t sp <*> go pren u

  go :: PartialRenaming -> Val -> IO Tm
  go pren t = case force t of
    VFlex m' sp | m == m'   -> throwIO UnifyError -- occurs check
                | otherwise -> goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x t  -> Lam x <$> go (lift pren) (t $$ VVar (cod pren))
    VPi x a b -> Pi x <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren))
    VU        -> pure U

-}
