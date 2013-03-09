{-# LANGUAGE RankNTypes, TypeOperators, ConstraintKinds, TypeFamilies, FlexibleContexts, DeriveFunctor, MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}

import Data.Monoid


newtype I a = I a
    deriving (Show, Functor)

newtype Constant b a = Constant b
    deriving (Show, Functor)

type Unit = Constant ()

data (f :+: g) a
    = InL (f a)
    | InR (g a)
    deriving (Show, Functor)

data (f :*: g) a
    = Pair (f a) (g a)
    deriving (Show, Functor)

newtype (r :~> f) a
    = Func (r -> f a)
    deriving (Functor)


type Algebra f a = f a -> a
type Coalgebra f a = a -> f a


newtype Free f = Free { getFree :: forall a. Algebra f a -> a }

free :: Algebra f a -> Free f -> a
free alg f = getFree f alg

freeConstruction :: (Functor f) => Algebra f (Free f)
freeConstruction f = Free $ \alg -> alg (fmap (free alg) f)

type MonoidF = Unit :+: (I :*: I)
type MonoidA m = Algebra MonoidF m

instance Monoid (Free MonoidF) where
    mempty = freeConstruction (InL (Constant ()))
    mappend a b = freeConstruction (InR (Pair (I a) (I b)))


type GeneratorF a = MonoidF :+: Constant a
type GeneratorA a m = Algebra (GeneratorF a) m


