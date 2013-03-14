{-# LANGUAGE TypeOperators, DeriveFunctor #-}

import Data.Functor.Identity
import Control.Applicative
import Control.Comonad
import Data.Monoid
import Data.Tree

class (Functor t) => Cotraversable t where
    cosequence :: (Comonad w) => w (t a) -> t (w a)

instance Cotraversable Identity where
    cosequence = Identity . fmap runIdentity

instance Cotraversable ((->) r) where
    cosequence w r = fmap ($ r) w

instance Cotraversable (Const b) where
    cosequence w = let Const x = extract w in Const x


data (f :*: g) x = Pair { proj1 :: f x, proj2 :: g x }
    deriving (Functor)

instance (Cotraversable f, Cotraversable g) => Cotraversable (f :*: g) where
    cosequence w = Pair (cosequence (fmap proj1 w)) (cosequence (fmap proj2 w))

data (f :+: g) x = InL (f x) | InR (g x)

