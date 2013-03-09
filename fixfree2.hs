{-# LANGUAGE RankNTypes, ConstraintKinds, FlexibleInstances, DoRec #-}

import Data.Functor.Identity
import Control.Monad.Fix
import Control.Monad

newtype Free c a = Free { getFree :: forall m b. c m => (a -> m b) -> m b }

instance Monad (Free c) where
    return x = Free ($ x)
    m >>= f = Free (\r -> getFree m (\x -> getFree (f x) r))

instance MonadFix (Free MonadFix) where
    mfix f = Free (=<< mfix (\x -> (getFree . f) x return))
        -- f :: a -> Free MonadFix a
        -- { MonadFix m }
        -- r :: a -> m b
        -- getFree . f :: a -> (a -> m a) -> m a
        -- \x -> (getFree . f) x return :: a -> m a
        -- mfix (\x -> (getFree . f) x return) :: m a
        --
        -- m b

ones :: Free MonadFix [Int]
ones = do
    rec x <- liftM (1:) $ return x
    return x

runFree :: Free MonadFix a -> a
runFree m = runIdentity $ getFree m return
