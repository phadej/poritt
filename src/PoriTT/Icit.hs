module PoriTT.Icit (
    Icit (..),
    prettyIcit,
    Arg (..),
) where

import PoriTT.Name
import PoriTT.PP

data Icit
    = Ecit  -- ^ explicit
    | Icit  -- ^ implicit
  deriving (Eq, Ord, Show)

prettyIcit :: Icit -> Doc
prettyIcit Ecit = "explicit"
prettyIcit Icit = "implicit"

data Arg a
    = ArgSel Selector
    | ArgApp Icit a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
