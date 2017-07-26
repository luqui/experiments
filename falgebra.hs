{-# LANGUAGE ConstraintKinds, DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving, MultiParamTypeClasses, PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TupleSections, TypeFamilies, TypeOperators, UndecidableInstances, UndecidableSuperClasses #-}

import Data.Functor.Classes
import Data.Functor.Compose

data Void
absurd :: Void -> a
absurd _ = error "absurd"

data Proxy t = Proxy

data (f <+> g) a = Inl (f a) | Inr (g a)
    deriving (Functor, Foldable, Traversable)

data (f <*> g) a = Product (f a) (g a)
    deriving (Functor, Foldable, Traversable)

-- F marks that this is to be used as a functor for the purposes of instances.
newtype F f a = F { getF :: f a }
    deriving (Functor, Applicative, Monad, Foldable, Traversable)


class (Functor f) => HasAlg f a where
    alg :: f a -> a

instance (Functor f) => HasAlg f () where
    alg _ = ()

instance (Functor f, HasAlg f a, HasAlg f b) => HasAlg f (a,b) where
    alg x = (alg (fmap fst x), alg (fmap snd x))
-- ... etc

instance (Traversable f, HasAlg f a) => HasAlg f (r -> a) where
    alg = getF . alg . fmap F

-- Unfortunate that we have to mark this specially.
instance (Applicative g, Traversable f, HasAlg f a) => HasAlg f (F g a) where
    alg = fmap alg . sequenceA

-- We can compose functors too, not just data!
instance (HasAlg f a, HasAlg g a) => HasAlg (Compose f g) a where
    alg = alg . fmap alg . getCompose

instance (HasAlg f a, HasAlg g a) => HasAlg (f <+> g) a where
    alg (Inl f) = alg f
    alg (Inr g) = alg g




class (Functor f) => HasCoalg f a where
    coalg :: a -> f a

instance (Functor f) => HasCoalg f Void where
    coalg = absurd

instance (Functor f, HasCoalg f a, HasCoalg f b) => HasCoalg f (Either a b) where
    coalg (Left x) = Left <$> coalg x
    coalg (Right x) = Right <$> coalg x

instance (Functor f, HasCoalg f a) => HasCoalg f (r,a) where
    coalg (r,x) = (r,) <$> coalg x

-- For pairs, there is also this.  It seems we would need some way to
-- differentiate "product"-like data from "environment"-like data.
--
--instance (Applicative f, HasCoalg f a, HasCoalg f b) => HasCoalg f (a,b) where
--    coalg (a,b) = (,) <$> coalg a <*> coalg b
--
-- There is also the dual for HasAlg using linear :: f (a,b) -> (a, f b)
-- (or many similar treatments) but this is not given by a standard typeclass 
-- so I have omitted it.

instance (Traversable g, Applicative f, HasCoalg f a) => HasCoalg f (F g a) where
    coalg = sequenceA . fmap coalg

instance (HasCoalg f a, HasCoalg g a) => HasCoalg (Compose f g) a where
    coalg = Compose . fmap coalg . coalg

instance (HasCoalg f a, HasCoalg g a) => HasCoalg (f <*> g) a where
    coalg x = Product (coalg x) (coalg x)



newtype Fix f = Fix { unFix :: f (Fix f) }

instance (Show1 f) => Show (Fix f) where
    showsPrec = showsUnaryWith showsPrec "Fix"


instance (Functor f) => HasAlg f (Fix f) where
    alg = Fix

instance (Functor f) => HasCoalg f (Fix f) where
    coalg = unFix


class (Functor (AlgebraOf c)) => Algebraic c where
    data AlgebraOf c :: * -> *
    stdAlgebra :: c a => AlgebraOf c a -> a

class (Functor (CoalgebraOf c)) => Coalgebraic c where
    data CoalgebraOf c :: * -> *
    stdCoalgebra :: c a => a -> CoalgebraOf c a
    

-- To mark the standard instance
newtype Std a = Std { getStd :: a }
    deriving (Show)

instance (Algebraic c, c a) => HasAlg (AlgebraOf c) (Std a) where
    alg = Std . stdAlgebra . fmap getStd

instance (Coalgebraic c, c a) => HasCoalg (CoalgebraOf c) (Std a) where
    coalg = fmap Std . stdCoalgebra . getStd
 


instance Algebraic Num where
    data AlgebraOf Num a = Plus a a | Minus a a | Times a a | Negate a | Abs a | Signum a | FromInteger Integer
        deriving (Show, Functor, Foldable, Traversable)
    stdAlgebra (Plus x y) = x + y
    stdAlgebra (Minus x y) = x - y
    stdAlgebra (Times x y) = x * y
    stdAlgebra (Negate x) = negate x
    stdAlgebra (Abs x) = abs x
    stdAlgebra (Signum x) = signum x
    stdAlgebra (FromInteger i) = fromInteger i


newtype New a = New { getNew :: a }
    deriving Show

instance (HasAlg (AlgebraOf Num) a) => Num (New a) where
    New x + New y = New $ alg (Plus x y)
    New x - New y = New $ alg (Minus x y)
    New x * New y = New $ alg (Times x y)
    negate (New x) = New $ alg (Negate x)
    abs (New x) = New $ alg (Abs x)
    signum (New x) = New $ alg (Signum x)
    fromInteger i = New $ alg (FromInteger i)


-- WOW (lol, was it worth it?)
test :: New (Std Int, Std Int)
test = 1


-- I think adapting this into the existing ecosystem is not going to happen
-- cleanly.  Sadly.  But for my own classes I could use it.
