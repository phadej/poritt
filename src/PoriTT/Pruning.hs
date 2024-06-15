module PoriTT.Pruning (
    Pruning (..),
    weakenPruning,
    emptyPruning,
) where

import PoriTT.Base

data Pruning ctx where
    Pruning :: Wk ctx ctx' -> Pruning ctx'

deriving instance Show (Pruning ctx)

weakenPruning :: Wk n m -> Pruning n -> Pruning m
weakenPruning w (Pruning xs) = Pruning (compWk xs w)

instance Weaken Pruning where
    weaken = weakenPruning

emptyPruning :: Size ctx -> Pruning ctx
emptyPruning = Pruning . go where
    go :: Size ctx -> Wk EmptyCtx ctx
    go SZ     = IdWk
    go (SS s) = SkipWk (go s)
