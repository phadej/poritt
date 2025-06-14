module PoriTT.Stage (
    -- * Stage
    Stage,
    stage0,
    stageDiff,
    prettyStage,
) where

import PoriTT.Base
import PoriTT.PP

-------------------------------------------------------------------------------
-- Name
-------------------------------------------------------------------------------

newtype Stage = Stage Int
  deriving (Eq, Ord, Show)

instance Enum Stage where
    succ (Stage s) = Stage (s + 1)
    pred (Stage s) = Stage (s - 1)

    toEnum = coerce
    fromEnum = coerce

stage0 :: Stage
stage0 = Stage 0

-- TODO: error check
stageDiff :: Stage -> Stage -> Natural
stageDiff (Stage a) (Stage b)
    | a < b     = error $ "stageDiff " ++ show (a, b) -- TODO: make safe
    | otherwise = fromIntegral (a - b)

prettyStage :: Stage -> Doc
prettyStage (Stage s) = ppInt s
