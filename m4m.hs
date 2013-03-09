{-# LANGUAGE ConstraintKinds, RankNTypes #-}

import Data.Monoid
import Control.Applicative
import Control.Monad (ap, liftM)

newtype CM c a = CM { getCM :: forall r. (c r) => (a -> r) -> r }

instance Monad (CM c) where
    return x = CM $ \r -> r x
    c >>= f = CM $ \r -> getCM c (\x -> getCM (f x) r)

instance Functor (CM c) where
    fmap = liftM

instance Applicative (CM c) where
    pure = return
    (<*>) = ap

fromList :: [a] -> CM Monoid a
fromList xs = CM $ \r -> mconcat (map r xs)

toList :: CM Monoid a -> [a]
toList c = getCM c (:[])

toFreeGen :: CM Monoid a -> FreeGen a
toFreeGen c = getCM c Leaf


data FreeGen a
    = Leaf a
    | Empty
    | Append (FreeGen a) (FreeGen a)
    deriving (Show)

depth :: Int -> FreeGen a -> FreeGen a
depth 0 _ = Empty
depth n (Leaf a) = Leaf a
depth n Empty = Empty
depth n (Append a b) = Append (depth (n-1) a) (depth (n-1) b)

instance Monoid (FreeGen a) where
    mempty = Empty
    mappend = Append
