module PoriTT.Path (
    Path (..),
    closeType,
) where

import PoriTT.Base
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Stage
import PoriTT.Term
import PoriTT.Value

-- | A "context zipper", used for creating types for fresh metas.
type Path :: Ctx -> Ctx -> Type
data Path ctx' ctx'' where
    PEnd    :: Path EmptyCtx EmptyCtx
    PDefine :: !(Path ctx' ctx'') -> !Name -> !Stage -> Path (S ctx') ctx''
    PBind   :: !(Path ctx' ctx'') -> !Name -> !Stage -> Term HasMetas ctx''-> Path (S ctx') (S ctx'')

deriving instance Show (Path ctx' ctx'')

-- | Create closed type from environment path-telescope.
--
-- First argument is the current stage.
closeType :: Stage -> Path ctx ctx' -> Either EvalError (Term HasMetas ctx' -> Term HasMetas EmptyCtx, Env ctx' Natural)
closeType cs = go where
    go ::  Path a b -> Either EvalError (Term HasMetas b -> Term HasMetas EmptyCtx, Env b Natural)
    go PEnd            = return (id, EmptyEnv)
    go (PDefine p _ _) = go p
    go (PBind p x s a) = do
        (mk, args) <- go p
        return (mk . Pie x Ecit (tyQuote s (qrenameTerm args a)), args :> stageDiff s cs)

    tyQuote :: Stage -> Term pass c -> Term pass c
    tyQuote s t = case compare s cs of
        EQ -> t
        GT -> tyQuote (pred s) (Cod $ quo t)
        LT -> error $ "tyQuote" ++ show (s, cs) -- TODO: can this happen?
