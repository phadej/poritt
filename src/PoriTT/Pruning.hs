{-# LANGUAGE UndecidableInstances #-}
module PoriTT.Pruning (
    -- * Pruning
    Pruning (..),
    weakenPruning,
    emptyPruning,
    -- * Qruning
    Qruning (..),
    weakenQruning,
    emptyQruning,
) where

import PoriTT.Base

-------------------------------------------------------------------------------
-- Quoting
-------------------------------------------------------------------------------

data Pruning ctx where
    Pruning :: Wk ctx ctx' -> Pruning ctx'

deriving instance Show (Pruning ctx)

weakenPruning :: Wk n m -> Pruning n -> Pruning m
weakenPruning w (Pruning xs) = Pruning (compWk xs w)

emptyPruning :: Size ctx -> Pruning ctx
emptyPruning = Pruning . go where
    go :: Size ctx -> Wk EmptyCtx ctx
    go SZ     = IdWk
    go (SS s) = SkipWk (go s)

-------------------------------------------------------------------------------
-- Pruning with quoted variables
-------------------------------------------------------------------------------

data Qruning ctx where
    Qruning :: Wk ctx ctx' -> Env ctx Natural -> Qruning ctx'

deriving instance Show (Qruning ctx)

weakenQruning :: Wk n m -> Qruning n -> Qruning m
weakenQruning w (Qruning xs ns) = Qruning (compWk xs w) ns

emptyQruning :: Size ctx -> Qruning ctx
emptyQruning size = Qruning (go size) EmptyEnv where
    go :: Size ctx -> Wk EmptyCtx ctx
    go SZ     = IdWk
    go (SS s) = SkipWk (go s)
