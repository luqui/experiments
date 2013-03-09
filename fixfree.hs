{-# LANGUAGE RankNTypes, GADTs, TupleSections #-}

import Control.Monad.Fix
import Control.Monad (liftM, (>=>))

data FFree f a where
    Pure   :: a -> FFree f a
    Effect :: f (FFree f a) -> FFree f a
    Fix    :: (s -> FFree f (s,a)) -> FFree f a

instance (Functor f) => Functor (FFree f) where
    fmap f (Pure x) = Pure (f x)    
    fmap f (Effect e) = Effect ((fmap.fmap) f e)
    fmap f (Fix c) = Fix ((fmap.fmap.fmap) f c)

instance (Functor f) => Monad (FFree f) where
    return = Pure
    Pure x >>= f = f x
    Effect k >>= f = Effect (fmap (>>= f) k)
    Fix c >>= f = Fix $ c >=> (\(s',x) -> liftM (s',) (f x))

instance (Functor f) => MonadFix (FFree f) where
    mfix f = Fix (liftM dup . f)

dup x = (x,x)
