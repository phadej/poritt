module PoriTT.Base (
    module X,
    type (:=),
    pattern (:=),
    pattern TODO,
    pattern NZ, pattern NS,
    MonadThrowError (..),
) where

import DeBruijn as X

import Control.Applicative        as X (Alternative (many, some, (<|>)), asum, liftA2, (<**>))
import Control.Monad              as X (guard, unless, void, when)
import Control.Monad.State.Class  as X (MonadState (get, put), modify')
import Data.ByteString            as X (ByteString)
import Data.Coerce                as X (coerce)
import Data.Foldable              as X (foldl', for_, toList, traverse_)
import Data.Foldable.WithIndex    as X (ifoldr, ifor_)
import Data.Function              as X ((&))
import Data.Kind                  as X (Type)
import Data.List.NonEmpty         as X (NonEmpty (..))
import Data.Map.Strict            as X (Map)
import Data.Maybe                 as X (catMaybes, isNothing)
import Data.Proxy                 as X (Proxy (..))
import Data.Semialign             as X (alignWith)
import Data.Semialign.Indexed     as X (ialignWith)
import Data.Set                   as X (Set)
import Data.SkewList.Lazy         as X (SkewList)
import Data.String                as X (IsString (..))
import Data.Text                  as X (Text)
import Data.Text.Short            as X (ShortText)
import Data.These                 as X (These (..))
import Data.Traversable           as X (for)
import Data.Traversable.WithIndex as X (ifor, itraverse)
import Data.Word                  as X (Word8)
import Debug.Trace                as X
import GHC.Exts                   as X (oneShot)
import GHC.Generics               as X (Generic)
import GHC.Stack                  as X (HasCallStack)
import Numeric.Natural            as X (Natural)
import Optics.Core                as X (Lens', set, view)

type a := b = (a, b)

pattern (:=) :: a -> b -> a := b
pattern a := b = (a, b)

infixr 0 :=

pattern TODO :: HasCallStack => () => a
pattern TODO <- _unused
  where TODO = error "TODO"

{-# COMPLETE TODO #-}

pattern NZ :: Natural
pattern NZ = 0

pattern NS :: Natural -> Natural
pattern NS n <- (safePred -> Just n)
  where NS n = n + 1

safePred :: Natural -> Maybe Natural
safePred 0 = Nothing
safePred n = Just (n - 1)

{-# COMPLETE NZ, NS #-}

-- | Class of monads were we can only throw errors, but not recover.
class Monad m => MonadThrowError e m | m -> e where
    throwError :: e -> m a

instance MonadThrowError e (Either e) where
    throwError = Left
