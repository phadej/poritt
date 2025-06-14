-- | Nicer combinators to construct 'Term' and 'Elim's.
module PoriTT.Nice (
    (@@),
    (.:),
    (~~>),
    (***),
    FromElim (..),
    emb_,
    ann_,
) where

import PoriTT.Base
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Term

-- | Infix function application
(@@) :: FromElim term => Elim pass ctx -> Term pass ctx -> term pass ctx
f @@ x = fromElim (App Ecit f x)
infixl 3 @@, .:

-- | Selector
(.:) :: FromElim term => Elim pass ctx -> Selector -> term pass ctx
e .: s = fromElim (Sel e s)

-- | Non-dependent function type
(~~>) :: Term pass ctx -> Term pass ctx -> Term pass ctx
a ~~> b = Pie "_" Ecit a (weaken wk1 b)
infixr 1 ~~>

-- | Non-dependent pair type
(***) :: Term pass ctx -> Term pass ctx -> Term pass ctx
a *** b = Sgm "_" Ecit a (weaken wk1 b)
infixr 2 ***

-- | Nicely embed elims into terms.
class    FromElim term where fromElim :: Elim pass ctx -> term pass ctx
instance FromElim Elim where fromElim = id
instance FromElim Term where fromElim = emb_

emb_ :: Elim pass ctx -> Term pass ctx
emb_ (Ann t _) = t
emb_ e         = Emb e

ann_ :: FromElim term => Term pass ctx -> Term pass ctx -> term pass ctx
ann_ (Emb e) _ = fromElim e
ann_ t       a = fromElim (Ann t a)
