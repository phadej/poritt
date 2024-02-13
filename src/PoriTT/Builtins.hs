module PoriTT.Builtins (
    evalDescGlobal,
    allTypeGlobal,
    allTermGlobal,
) where

import PoriTT.Base
import PoriTT.Eval
import PoriTT.Global
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Nice
import PoriTT.Term

-- $setup
-- >>> import PoriTT.Info

mkGlobal :: Name -> Term NoMetas EmptyCtx -> Term NoMetas EmptyCtx -> Global
mkGlobal name tm ty = Global
    { name   = name
    , term   = Ann tm ty
    , typ    = ty'
    , val    = vann tm' ty'
    , inline = False
    }
  where
    tm' = evalTerm SZ EmptyEnv tm
    ty' = evalTerm SZ EmptyEnv ty

-------------------------------------------------------------------------------
-- evalDesc
-------------------------------------------------------------------------------

-- | Evaluate description: @evalDesc@
--
-- >>> infoGlobal evalDescGlobal
-- defined evalDesc
--   : Desc -> U -> U
--   = \ d X ->
--       indDesc
--         d
--         (\ _ -> U)
--         Unit
--         (\ S D F -> exists (s : S) * F s)
--         (\ D F -> X * F)
--
evalDescGlobal :: Global
evalDescGlobal = mkGlobal "evalDesc" evalDescTerm evalDescType

evalDescType :: Term pass ctx
evalDescType = Pie "_" Ecit Dsc $ Pie "_" Ecit Uni Uni

evalDescTerm :: Term pass ctx
evalDescTerm = Lam "d" Ecit $ Lam "X" Ecit $ Emb $ DeI
    (Var I1)
    (Lam "_" Ecit Uni)
    One
    (Lam "S" Ecit $ Lam "D" Ecit $ Lam "F" Ecit $ Sgm "s" Ecit (Emb (Var I2)) (Emb (App Ecit (Var I1) (Emb (Var IZ)))))
    (Lam "D" Ecit $ Lam "F" Ecit $ Sgm "_" Ecit (Emb (Var I2)) (Emb (Var I1)))

-------------------------------------------------------------------------------
-- All
-------------------------------------------------------------------------------

{- |

>>> infoGlobal allTypeGlobal
defined All
  : forall (D : Desc) (X : U) -> (X -> U) -> evalDesc D X -> U
  = \ D' X P ->
      indDesc
        D'
        (\ D -> evalDesc D X -> U)
        (\ xs -> Unit)
        (\ S D Dm xs -> Dm (xs .fst) (xs .snd))
        (\ D Dm xs -> P (xs .fst) * Dm (xs .snd))

-}
allTypeGlobal :: Global
allTypeGlobal = mkGlobal "All" allTypeTerm allTypeType

allTypeType :: Term pass ctx
allTypeType = Pie "D" Ecit Dsc $ Pie "X" Ecit Uni $ Pie "P" Ecit (Pie "_" Ecit (Emb (Var IZ)) Uni) $
    Pie "xs" Ecit (Gbl evalDescGlobal @@ var I2 @@ var I1) Uni

allTypeTerm :: Term pass ctx
allTypeTerm =
    Lam "D'" Ecit $ Lam "X" Ecit $ Lam "P" Ecit $ Emb $ DeI
        (var I2)
        (Lam "D" Ecit $ Pie "xs" Ecit (Gbl evalDescGlobal @@ var IZ @@ var I2) Uni)
        (Lam "xs" Ecit  One)
        (Lam "S" Ecit $ Lam "D" Ecit $ Lam "Dm" Ecit $ Lam "xs" Ecit $ var I1 @@ (var IZ .: "fst") @@ (var IZ .: "snd"))
        (Lam "D" Ecit $ Lam "Dm" Ecit $ Lam "xs" Ecit $ var I3 @@ (var IZ .: "fst") *** var I1 @@ (var IZ .: "snd"))

-------------------------------------------------------------------------------
-- all
-------------------------------------------------------------------------------

{- |

>>> infoGlobal allTermGlobal
defined all
  : forall
      (D : Desc) (X : U) (P : X -> U) ->
      (forall (x : X) -> P x) -> forall (xs : evalDesc D X) -> All D X P xs
  = \ D' X P p ->
      indDesc
        D'
        (\ D -> forall (xs : evalDesc D X) -> All D X P xs)
        (\ xs -> tt)
        (\ S D allD xs -> allD (xs .fst) (xs .snd))
        (\ D allD xs -> p (xs .fst) , allD (xs .snd))

-}
allTermGlobal :: Global
allTermGlobal = mkGlobal "all" allTermTerm allTermType

allTermType :: Term pass ctx
allTermType =
  Pie "D" Ecit Dsc $
  Pie "X" Ecit Uni $
  Pie "P" Ecit (var IZ ~~> Uni) $
  Pie "p" Ecit (Pie "x" Ecit (var I1) $ var I1 @@ var IZ) $
  Pie "xs" Ecit (Gbl evalDescGlobal @@ var I3 @@ var I2) $
  Gbl allTypeGlobal @@ var I4 @@ var I3 @@ var I2 @@ var IZ

allTermTerm :: Term pass ctx
allTermTerm = Lam "D'" Ecit $ Lam "X" Ecit $ Lam "P" Ecit $ Lam "p" Ecit $ Emb $ DeI (var I3)
    (Lam "D" Ecit $ Pie "xs" Ecit (Gbl evalDescGlobal @@ var IZ @@ var I3) $
      Gbl allTypeGlobal @@ var I1 @@ var I4 @@ var I3 @@ var IZ)
    (Lam "xs" Ecit Tht)
    (Lam "S" Ecit $ Lam "D" Ecit $ Lam "allD" Ecit $ Lam "xs" Ecit $ var I1 @@ (var IZ .: "fst") @@ (var IZ .: "snd"))
    (Lam "D" Ecit $ Lam "allD" Ecit $ Lam "xs" Ecit $ Mul Ecit (var I3 @@ (var IZ .: "fst")) (var I1 @@ (var IZ .: "snd")))
