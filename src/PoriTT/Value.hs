module PoriTT.Value (
    -- * Values
    VTerm (..),
    VElim (..),
    Spine (..),
    coeNoMetasVElim,
    -- ** Closure
    Closure (..),
    ClosureE,
    ClosureT,
    valZ,
    -- ** Evaluation context
    EvalEnv,
    EvalElim (..),
    evalZ,
    velim,
    emptyEvalEnv,
    -- ** Evaluation error
    EvalError (..),
    -- * Staging values
    STerm (..),
    SElim (..),
    svalZ,
) where

import Unsafe.Coerce (unsafeCoerce)

import PoriTT.Base
import PoriTT.Enum
import PoriTT.Icit
import PoriTT.Name
import PoriTT.Term
import PoriTT.Meta

import {-# SOURCE #-} PoriTT.Global (Global)

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

-------------------------------------------------------------------------------
-- VTerm and VElim
-------------------------------------------------------------------------------

-- | Semantic term
type VTerm :: TermPass -> Ctx -> Type
data VTerm pass ctx where
    VPie :: !Name -> !Icit -> (VTerm pass ctx) -> !(ClosureT pass ctx) -> VTerm pass ctx
    VLam :: !Name -> !Icit -> !(ClosureT pass ctx)  -> VTerm pass ctx
    VUni :: VTerm pass ctx
    VOne :: VTerm pass ctx
    VTht :: VTerm pass ctx
    VDsc :: VTerm pass ctx
    VDe1 :: VTerm pass ctx
    VDeS :: VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx
    VDeX :: VTerm pass ctx -> VTerm pass ctx
    VMuu :: VTerm pass ctx -> VTerm pass ctx
    VCon :: VTerm pass ctx -> VTerm pass ctx
    VSgm :: !Name -> !Icit -> (VTerm pass ctx) -> !(ClosureT pass ctx) -> VTerm pass ctx
    VMul :: !Icit -> VTerm pass ctx -> VTerm pass ctx -> VTerm pass ctx
    VEIx :: !EnumIdx -> VTerm pass ctx
    VFin :: ![Label] -> VTerm pass ctx
    VCod :: VTerm pass ctx -> VTerm pass ctx
    VQuo :: STerm pass ctx -> VTerm pass ctx -> VTerm pass ctx -- we preserve the syntax, but also evalute.
    VEmb :: VElim pass ctx -> VTerm pass ctx  -- no VAnn

-- | Semantic elimination
type VElim :: TermPass -> Ctx -> Type
data VElim pass ctx where
    VErr :: EvalError -> VElim pass ctx
    VAnn :: VTerm pass ctx -> VTerm pass ctx -> VElim pass ctx
    VGbl :: !Global -> !(Spine pass ctx) -> VElim pass ctx -> VElim pass ctx
    VRgd :: Lvl ctx -> Spine pass ctx -> VElim pass ctx
    VFlx :: MetaVar -> Spine HasMetas ctx -> VElim HasMetas ctx

deriving instance Show (VTerm pass ctx)
deriving instance Show (VElim pass ctx)

instance Sinkable (VTerm pass) where
    mapLvl _ VUni            = VUni
    mapLvl _ VOne            = VOne
    mapLvl _ VTht            = VTht
    mapLvl _ VDsc            = VDsc
    mapLvl _ VDe1            = VDe1
    mapLvl f (VDeS t s)      = VDeS (mapLvl f t) (mapLvl f s)
    mapLvl f (VDeX t)        = VDeX (mapLvl f t)
    mapLvl f (VMuu t)        = VMuu (mapLvl f t)
    mapLvl f (VCon t)        = VCon (mapLvl f t)
    mapLvl f (VLam x i clos) = VLam x i (mapLvl f clos)
    mapLvl f (VPie x i a b)  = VPie x i (mapLvl f a) (mapLvl f b)
    mapLvl f (VSgm x i a b)  = VSgm x i (mapLvl f a) (mapLvl f b)
    mapLvl f (VMul i t s)    = VMul i (mapLvl f t) (mapLvl f s)
    mapLvl _ (VEIx i)        = VEIx i
    mapLvl _ (VFin ls)       = VFin ls
    mapLvl f (VCod a)        = VCod (mapLvl f a)
    mapLvl f (VQuo t t')     = VQuo (mapLvl f t) (mapLvl f t')
    mapLvl f (VEmb e)        = VEmb (mapLvl f e)

instance Sinkable (VElim pass) where
    mapLvl _ (VErr msg)    = VErr msg
    mapLvl f (VRgd l sp)   = VRgd (mapLvl f l) (mapLvl f sp)
    mapLvl f (VFlx m sp)   = VFlx m (mapLvl f sp)
    mapLvl f (VGbl g sp t) = VGbl g (mapLvl f sp) (mapLvl f t)
    mapLvl f (VAnn t s)    = VAnn (mapLvl f t) (mapLvl f s)

-- | 'VElim' with no metas can be coerced to 'VElim' with metas.
coeNoMetasVElim :: VElim NoMetas ctx -> VElim pass ctx
coeNoMetasVElim = unsafeCoerce

-------------------------------------------------------------------------------
-- Spine
-------------------------------------------------------------------------------

-- | Spine of neutral terms ('VRgd').
type Spine :: TermPass -> Ctx -> Type
data Spine pass ctx
    = VNil
    | VApp !(Spine pass ctx) !Icit (VTerm pass ctx)
    | VSel !(Spine pass ctx) !Selector
    | VSwh !(Spine pass ctx) (VTerm pass ctx) !(EnumList (VTerm pass ctx)) -- Note: motive is lazy as we don't evaluate it. It's needed for type-checking only.
    | VDeI !(Spine pass ctx) (VTerm pass ctx) (VTerm pass ctx) (VTerm pass ctx) (VTerm pass ctx)
    | VInd !(Spine pass ctx) (VTerm pass ctx) (VTerm pass ctx)
    | VSpl !(Spine pass ctx)
  deriving Show

instance Sinkable (Spine pass) where
    mapLvl _ VNil              = VNil
    mapLvl f (VApp xs i x)     = VApp (mapLvl f xs) i (mapLvl f x)
    mapLvl f (VSel xs s)       = VSel (mapLvl f xs) s
    mapLvl f (VSwh xs m rs)    = VSwh (mapLvl f xs) (mapLvl f m) (fmap (mapLvl f) rs)
    mapLvl f (VDeI xs m x y z) = VDeI (mapLvl f xs) (mapLvl f m) (mapLvl f x) (mapLvl f y) (mapLvl f z)
    mapLvl f (VInd xs m t)     = VInd (mapLvl f xs) (mapLvl f m) (mapLvl f t)
    mapLvl f (VSpl xs)         = VSpl (mapLvl f xs)

-------------------------------------------------------------------------------
-- Closure
-------------------------------------------------------------------------------

-- Terms in context
type EvalElim :: TermPass -> Ctx -> Type
data EvalElim pass ctx = EvalElim (VElim pass ctx) (SElim pass ctx)

deriving instance Show (EvalElim pass ctx)

velim :: VElim pass ctx' -> EvalElim pass ctx'
velim v = EvalElim v (SErr EvalErrorStg)

instance Sinkable (EvalElim pass) where
    mapLvl f (EvalElim e s) = EvalElim (mapLvl f e) (mapLvl f s)

type EvalEnv :: TermPass -> Ctx -> Ctx -> Type
type EvalEnv pass ctx ctx' = Env ctx (EvalElim pass ctx')

emptyEvalEnv :: EvalEnv pass EmptyCtx EmptyCtx
emptyEvalEnv = EmptyEnv

type Closure :: (TermPass -> Ctx -> Type) -> TermPass -> Ctx -> Type
data Closure term pass ctx' where
    Closure :: EvalEnv pass ctx ctx' -> term pass (S ctx) -> Closure term pass ctx'

deriving instance (forall ctx'. Show (term pass ctx')) => Show (Closure term pass ctx)

type ClosureE = Closure Elim
type ClosureT = Closure Term

instance Sinkable (Closure term pass) where
    mapLvl f (Closure env t) = Closure (fmap (mapLvl f) env) t

valZ :: Size ctx -> VElim pass (S ctx)
valZ s = VRgd (lvlZ s) VNil

evalZ :: Size ctx -> EvalElim pass (S ctx)
evalZ s = EvalElim (valZ s) (svalZ s)

-------------------------------------------------------------------------------
-- Symbolic terms
-------------------------------------------------------------------------------

type STerm :: TermPass -> Ctx -> Type
data STerm pass ctx where
    SPie :: !Name -> !Icit -> STerm pass ctx -> !(ClosureT pass ctx) -> STerm pass ctx
    SLam :: !Name -> !Icit -> !(ClosureT pass ctx) -> STerm pass ctx
    SSgm :: !Name -> !Icit -> STerm pass ctx -> !(ClosureT pass ctx) -> STerm pass ctx
    SMul :: !Icit -> STerm pass ctx -> STerm pass ctx -> STerm pass ctx
    SEIx :: EnumIdx -> STerm pass ctx
    SFin :: [Label] -> STerm pass ctx
    SUni :: STerm pass ctx
    SOne :: STerm pass ctx
    STht :: STerm pass ctx
    SDsc :: STerm pass ctx
    SDe1 :: STerm pass ctx
    SDeS :: STerm pass ctx -> STerm pass ctx -> STerm pass ctx
    SDeX :: STerm pass ctx -> STerm pass ctx
    SMuu :: STerm pass ctx -> STerm pass ctx
    SCon :: STerm pass ctx -> STerm pass ctx
    SCod :: STerm pass ctx -> STerm pass ctx
    SQuo :: STerm pass ctx -> STerm pass ctx
    SEmb :: SElim pass ctx -> STerm pass ctx

type SElim :: TermPass -> Ctx -> Type
data SElim pass ctx where
    SErr :: EvalError -> SElim pass ctx
    SVar :: Lvl ctx -> SElim pass ctx
    SRgd :: Int -> SElim pass ctx -- TODO
    SGbl :: Global -> SElim pass ctx
    SApp :: !Icit -> SElim pass ctx -> STerm pass ctx -> SElim pass ctx
    SSel :: SElim pass ctx -> Selector -> SElim pass ctx
    SSwh :: SElim pass ctx -> STerm pass ctx -> EnumList (STerm pass ctx) -> SElim pass ctx
    SDeI :: SElim pass ctx -> STerm pass ctx -> STerm pass ctx -> STerm pass ctx -> STerm pass ctx -> SElim pass ctx
    SInd :: SElim pass ctx -> STerm pass ctx -> STerm pass ctx -> SElim pass ctx
    SAnn :: STerm pass ctx -> STerm pass ctx -> SElim pass ctx
    SLet :: !Name -> SElim pass ctx -> !(ClosureE pass ctx) -> SElim pass ctx
    SSpl :: SElim pass ctx -> VElim pass ctx -> SElim pass ctx

deriving instance Show (STerm pass ctx)
deriving instance Show (SElim pass ctx)

instance Sinkable (STerm pass) where
    mapLvl f (SPie x i a b)  = SPie x i (mapLvl f a) (mapLvl f b)
    mapLvl f (SLam x i clos) = SLam x i (mapLvl f clos)
    mapLvl f (SSgm x i a b)  = SSgm x i (mapLvl f a) (mapLvl f b)
    mapLvl f (SMul i t s)    = SMul i (mapLvl f t) (mapLvl f s)
    mapLvl _ SUni            = SUni
    mapLvl _ SOne            = SOne
    mapLvl _ STht            = STht
    mapLvl _ SDsc            = SDsc
    mapLvl _ SDe1            = SDe1
    mapLvl f (SDeS t r)      = SDeS (mapLvl f t) (mapLvl f r)
    mapLvl f (SDeX t)        = SDeX (mapLvl f t)
    mapLvl _ (SEIx i)        = SEIx i
    mapLvl _ (SFin ls)       = SFin ls
    mapLvl f (SMuu a)        = SMuu (mapLvl f a)
    mapLvl f (SCon a)        = SCon (mapLvl f a)
    mapLvl f (SCod a)        = SCod (mapLvl f a)
    mapLvl f (SQuo t)        = SQuo (mapLvl f t)
    mapLvl f (SEmb e)        = SEmb (mapLvl f e)

instance Sinkable (SElim pass) where
    mapLvl _ (SErr err)       = SErr err
    mapLvl f (SVar x)         = SVar (mapLvl f x)
    mapLvl _ (SGbl g)         = SGbl g
    mapLvl f (SApp i g t)     = SApp i (mapLvl f g) (mapLvl f t)
    mapLvl f (SSel e t)       = SSel (mapLvl f e) t
    mapLvl f (SSwh xs m rs)   = SSwh (mapLvl f xs) (mapLvl f m) (fmap (mapLvl f) rs)
    mapLvl f (SInd e m t)     = SInd (mapLvl f e) (mapLvl f m) (mapLvl f t)
    mapLvl f (SDeI e m x y z) = SDeI (mapLvl f e) (mapLvl f m) (mapLvl f x) (mapLvl f y) (mapLvl f z)
    mapLvl f (SSpl e e')      = SSpl (mapLvl f e) (mapLvl f e')
    mapLvl f (SLet x a b)     = SLet x (mapLvl f a) (mapLvl f b)
    mapLvl f (SAnn t s)       = SAnn (mapLvl f t) (mapLvl f s)

svalZ :: Size ctx -> SElim pass (S ctx)
svalZ s = SVar (lvlZ s)
