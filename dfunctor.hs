{-# LANGUAGE TypeFamilies, DeriveFunctor, TypeOperators, FlexibleContexts, TupleSections #-}

import Data.Functor.Identity
import Control.Applicative
import Control.Arrow (first)
import Data.Tuple (swap)


strength :: (Functor f) => (a, f b) -> f (a,b)
strength (x, f) = fmap (x,) f

newtype (g ° f) x = Compose { getCompose :: g (f x) }
    deriving (Functor)

data (g :*: f) x = Pair (g x) (f x)
    deriving (Functor)

fromPair :: (f a, g a) -> (f :*: g) a
fromPair (x, y) = Pair x y

data (g :+: f) x = Inl (g x) | Inr (f x)
    deriving (Functor)

class (Functor (D f), Functor f) => Differentiable f where
    type D f :: * -> *
    deriv :: f a -> f (a, D f a)

instance Differentiable Identity where
    type D Identity = Const ()
    deriv (Identity x) = Identity (x, Const ())

instance Differentiable Maybe where
    type D Maybe = Const ()
    deriv Nothing = Nothing
    deriv (Just x) = Just (x, Const ())

instance Differentiable (Either a) where
    type D (Either a) = Const ()
    deriv (Left x) = Left x
    deriv (Right x) = Right (x, Const ())

instance (Differentiable g, Differentiable f) => Differentiable (g :+: f) where
    type D (g :+: f) = D g :+: D f
    deriv (Inl x) = Inl ((fmap.fmap) Inl (deriv x))
    deriv (Inr x) = Inr ((fmap.fmap) Inr (deriv x))

instance (Differentiable g, Differentiable f) => Differentiable (g :*: f) where
    type D (g :*: f) = (D g :*: f) :+: (g :*: D f)
    deriv (Pair x y) = Pair ((fmap.fmap) (Inl . (`Pair` y)) (deriv x)) 
                            ((fmap.fmap) (Inr . (x `Pair`)) (deriv y))

instance (Differentiable g, Differentiable f) => Differentiable (g ° f) where
    type D (g ° f)   = (D g ° f) :*: D f
    deriv (Compose x) = Compose $ 
        fmap (fmap (fmap fromPair . strength) . strength . swap . fmap Compose . first deriv) 
             (deriv x)


