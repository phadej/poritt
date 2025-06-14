module PoriTT.Macro (
    Macro (..),
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.Well

-- | A macro is expanded in renamer.
data Macro where
    Macro :: Name -> Env arity Name -> Well NoTerms arity -> Macro
