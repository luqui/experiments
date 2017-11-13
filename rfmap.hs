{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances, UndecidableInstances, FunctionalDependencies #-}

import Prelude hiding (id, (.))
import Control.Category
import Data.Functor.Identity
import Data.Functor.Compose

data Iso a b = Iso (a -> b) (b -> a)

instance Category Iso where
    id = Iso id id
    Iso g g' . Iso f f' = Iso (g . f) (f' . g')

inverse :: Iso a b -> Iso b a
inverse (Iso f f') = Iso f' f

apply :: Iso a b -> a -> b
apply (Iso f _) = f

fmapIso :: (Functor f) => Iso a b -> Iso (f a) (f b)
fmapIso (Iso f f') = Iso (fmap f) (fmap f')

class (Functor g) => Functorize a f g | a f -> g, g a -> f where
    functorize :: Iso f (g a)

instance Functorize Int Int Identity where
    functorize = Iso Identity runIdentity
instance Functorize Char Char Identity where
    functorize = Iso Identity runIdentity
    
instance (Functorize a f g) => Functorize a (Maybe f) (Compose Maybe g) where
    functorize = Iso Compose getCompose . fmapIso functorize
instance (Functorize a f g) => Functorize a [f] (Compose [] g) where
    functorize = Iso Compose getCompose . fmapIso functorize

rfmap :: (Functorize a f g, Functorize b f' g) => (a -> b) -> (f -> f')
rfmap f = apply (inverse functorize) . fmap f . apply functorize

check :: [[Maybe Int]]
check = rfmap (+ (1 :: Int)) [[Just (1 :: Int),Just 2],[Nothing,Just 4,Just 5]]
--[[Just 2,Just 3],[Nothing,Just 5,Just 6]]
