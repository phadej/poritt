{-# LANGUAGE UnboxedSums   #-}
{-# LANGUAGE UnboxedTuples #-}
module PoriTT.ExceptState (
    ExceptState,
    runExceptState,
    evalExceptState,
) where

import PoriTT.Base

import Control.Monad (ap)

type ExceptState' e s a = s -> (# e | (# s, a #) #)

newtype ExceptState e s a = ExceptState_ (ExceptState' e s a)

runExceptState :: ExceptState e s a -> s -> Either e (s, a)
runExceptState m s = case runExceptState_ m s of
    (# err | #)         -> Left err
    (# | (# s', x #) #) -> Right (s', x)

evalExceptState :: ExceptState e s a -> s -> Either e a
evalExceptState m s = case runExceptState_ m s of
    (# err | #)        -> Left err
    (# | (# _, x #) #) -> Right x

runExceptState_ :: ExceptState e s a -> ExceptState' e s a
runExceptState_ (ExceptState f) = f

pattern ExceptState :: ExceptState' e s a -> ExceptState e s a
pattern ExceptState f <- ExceptState_ f
  where ExceptState f = ExceptState (oneShot f)
{-# COMPLETE ExceptState #-}

instance Functor (ExceptState e s) where
    fmap f (ExceptState g) = ExceptState $ \s -> case g s of
        (# err | #) -> (# err | #)
        (# | (# s', x #) #) -> (# | (# s', f x #) #)

instance Applicative (ExceptState e s) where
    pure x = ExceptState (\s -> (# | (# s, x #) #))
    (<*>) = ap
    a *> b = ExceptState $ \s -> case runExceptState_ a s of
        (# err | #)          ->(# err | #)
        (# | (# s', _ #) #) -> runExceptState_ b s'

instance Monad (ExceptState e s) where
    m >>= k = ExceptState $ \s -> case runExceptState_ m s of
        (# err | #)          ->(# err | #)
        (# | (# s', x #) #) -> runExceptState_ (k x) s'

    (>>) = (*>)

instance MonadState s (ExceptState e s) where
    put s = ExceptState $ \_ -> (#| (# s, () #) #)
    get   = ExceptState $ \s -> (#| (# s, s #) #)
