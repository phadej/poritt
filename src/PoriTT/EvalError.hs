module PoriTT.EvalError (
    EvalError (..),
) where

-------------------------------------------------------------------------------
-- Evaluation errors
-------------------------------------------------------------------------------

-- | Evaluation error.
--
-- These shouldn't happen if we evaluate type-correct code.
--
data EvalError
    = EvalErrorApp  -- ^ error in function application
    | EvalErrorSel  -- ^ error in selector application
    | EvalErrorSwh  -- ^ error in @switch@
    | EvalErrorDeI  -- ^ error in @indDesc@
    | EvalErrorInd  -- ^ error in @ind@
    | EvalErrorSpl  -- ^ error in @spl@
    | EvalErrorStg  -- ^ error in staging.
  deriving Show
