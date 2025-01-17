{-# LANGUAGE UndecidableInstances #-}
module PoriTT.Pruning (
    -- * Pruning
    Pruning (..),
    weakenPruning,
    emptyPruning,
    -- * Qruning
    Qruning (..),
    weakenQruning,
    weakenQruningL,
    compQrunning,
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

data Qruning ctx ctx' where
    NilQ :: Qruning EmptyCtx EmptyCtx
    SkipQ :: Qruning ctx ctx' -> Qruning ctx (S ctx')
    KeepQ :: Int -> Qruning ctx ctx' -> Qruning (S ctx) (S ctx')

deriving instance Show (Qruning ctx ctx')

compQrunning :: Qruning a b -> Qruning b c -> Qruning a c
compQrunning NilQ        q           = q
compQrunning w           (SkipQ   q) = SkipQ   (compQrunning w q)
compQrunning (SkipQ   w) (KeepQ _ q) = SkipQ   (compQrunning w q)
compQrunning (KeepQ j w) (KeepQ i q) = KeepQ (i + j) (compQrunning w q)

weakenQruning :: Wk n m -> Qruning p n -> Qruning p m
weakenQruning IdWk       q           = q
weakenQruning (SkipWk w) q           = SkipQ   (weakenQruning w q)
weakenQruning (KeepWk w) (SkipQ   q) = SkipQ   (weakenQruning w q)
weakenQruning (KeepWk w) (KeepQ i q) = KeepQ i (weakenQruning w q)

weakenQruningL :: Wk a b -> Qruning b c -> Qruning a c
weakenQruningL IdWk       q           = q
weakenQruningL w          (SkipQ   q) = SkipQ   (weakenQruningL w q)
weakenQruningL (SkipWk w) (KeepQ _ q) = SkipQ   (weakenQruningL w q)
weakenQruningL (KeepWk w) (KeepQ i q) = KeepQ i (weakenQruningL w q)
