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

-- | A "context zipper", used for creating types for fresh metas.
type Path :: Ctx -> Ctx -> Ctx -> Type
data Path ctx ctx' ctx'' where
    PEnd    :: Path ctx ctx ctx
    PDefine :: !(Path ctx ctx' ctx'') -> !Name -> !Stage -> Path ctx (S ctx') ctx''
    PBind   :: !(Path ctx ctx' ctx'') -> !Name -> !Stage -> (Term HasMetas ctx'')-> Path ctx (S ctx') (S ctx'')

deriving instance Show (Path ctx ctx' ctx'')

-- | Create closed type from environment path-telescope.
--
-- First argument is the current stage.
closeType :: Stage -> Size ctx'' -> Term HasMetas ctx'' -> Path ctx ctx' ctx'' -> Either EvalError (Term HasMetas ctx)
closeType _  _      b PEnd              = pure b
closeType cs s      b (PDefine p _s _x) = closeType cs s b p
closeType cs (SS s) b (PBind p x _s a)  = do
    closeType cs s (Pie x Ecit a b) p
