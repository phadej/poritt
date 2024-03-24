module PoriTT.Path (
    Path (..),
    closeType,
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.Term
import PoriTT.Icit
import PoriTT.Value
import PoriTT.Quote

-- | A "context zipper", used for creating types for fresh metas.
type Path :: Ctx -> Ctx -> Ctx -> Type
data Path ctx ctx' ctx'' where
    PEnd    :: Path ctx ctx ctx
    PDefine :: !(Path ctx ctx' ctx'') -> !Name -> Path ctx (S ctx') ctx''
    PBind   :: !(Path ctx ctx' ctx'') -> !Name -> (VTerm HasMetas ctx'')-> Path ctx (S ctx') (S ctx'')

closeType :: Size ctx'' -> VTerm HasMetas ctx'' -> Path ctx ctx' ctx'' -> Either EvalError (VTerm HasMetas ctx)
closeType _      b PEnd           = pure b
closeType s      b (PDefine p _x) = closeType s b p
closeType (SS s) b (PBind p x a)  = do
    b' <- quoteTerm UnfoldNone (SS s) b
    closeType s (VPie x Ecit a (Closure (tabulateEnv s (evalVar s)) b')) p
  where
    evalVar :: Size n -> Idx n -> EvalElim 'HasMetas n
    evalVar s' i = EvalElim (VVar l) (SVar l) where !l = idxToLvl s' i
