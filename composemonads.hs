{-# LANGUAGE FlexibleContexts, StandaloneDeriving #-}

import Data.Functor.Compose
import Data.Traversable
import Control.Applicative
import Control.Monad
import Test.QuickCheck

instance (Applicative f, Applicative g, Monad f, Monad g, Traversable g) => Monad (Compose f g) where
    return = Compose . return . return
    m >>= f = join (fmap f m)

instance (Eq (f (g a))) => Eq (Compose f g a) where
    a == b = getCompose a == getCompose b

joinC :: (Applicative f, Applicative g, Monad f, Monad g, Traversable g) => f (g (f (g a))) -> f (g a)
joinC = fmap join . join . fmap sequenceA

joinC' :: (Applicative f, Applicative g, Monad f, Monad g, Traversable g) => Compose f g (Compose f g a) -> Compose f g a
joinC' = Compose . joinC . getCompose . fmap getCompose 

toCompose :: (Functor f, Functor g) => f (g (f (g a))) -> Compose f g (Compose f g a)
toCompose = fmap Compose . Compose

deriving instance (Show (f (g a))) => Show (Compose f g a)

type F = Maybe
type G = Maybe
type FG a = F (G a)
type A = Bool

prop_unit1 :: FG A -> Bool
prop_unit1 xs = join (fmap return xs') == xs'
    where xs' = Compose xs

prop_unit2 :: FG A -> Bool
prop_unit2 xs = join (return xs') == xs'
    where xs' = Compose xs

prop_assoc :: FG (FG (FG (FG (FG (FG A))))) -> Bool
prop_assoc xs = join (fmap join xs') == join (join xs')
    where 
    xs' = (fmap.fmap.fmap.fmap) toCompose . (fmap.fmap) toCompose . toCompose $ xs

