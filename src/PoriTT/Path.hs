module PoriTT.Path (
    Path (..),
    closeType,
) where

import PoriTT.Base
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Quote
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Value
import PoriTT.Pruning

-- | A "context zipper", used for creating types for fresh metas.
type Path :: Ctx -> Ctx -> Type
data Path ctx' ctx'' where
    PEnd    :: Path EmptyCtx EmptyCtx
    PDefine :: !(Path ctx' ctx'') -> !Name -> !Stage -> Path (S ctx') ctx''
    PBind   :: !(Path ctx' ctx'') -> !Name -> !Stage -> (Term HasMetas ctx'')-> Path (S ctx') (S ctx'')

deriving instance Show (Path ctx' ctx'')

-- | Create closed type from environment path-telescope.
--
-- First argument is the current stage.
closeType :: Stage -> Size ctx'' -> Term HasMetas ctx'' -> Path ctx' ctx'' -> Either EvalError (Term HasMetas EmptyCtx)
closeType _  _      b PEnd              = pure b
closeType cs s      b (PDefine p _s _x) = closeType cs s b p
closeType cs (SS s) b (PBind p x _s a)  = do
    closeType cs s (Pie x Ecit a b) p

type Args ctx = Size ctx

closeType2 :: Stage -> Size ctx'' -> Path ctx' ctx'' -> Either EvalError (Term HasMetas ctx'' -> Term HasMetas EmptyCtx, Args ctx'')
closeType2 = TODO
