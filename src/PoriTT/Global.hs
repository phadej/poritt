module PoriTT.Global (
    Global (..),
    prettyGlobal,
) where

import PoriTT.Base
import PoriTT.Name
import PoriTT.PP
import PoriTT.Term
import PoriTT.Value (VElim, VTerm)

data Global = Global
    { name   :: !Name
    , term   :: Elim NoMetas EmptyCtx
    , typ    :: VTerm NoMetas EmptyCtx
    , val    :: VElim NoMetas EmptyCtx
    , inline :: Bool
    }

instance Show Global where
    showsPrec d g = showsPrec d g.name

prettyGlobal :: Global -> Doc
prettyGlobal g = ppAnnotate AGbl (prettyName g.name)
