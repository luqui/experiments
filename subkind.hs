{-# LANGUAGE PolyKinds, MultiParamTypeClasses, FunctionalDependencies, ConstraintKinds, FlexibleInstances, TypeOperators, RankNTypes, ExistentialQuantification, DeriveFunctor, StandaloneDeriving, ScopedTypeVariables, UndecidableInstances #-}

import Prelude hiding (id,(.),fst,snd,Functor)
import qualified Prelude

data Proxy t = Proxy

class Trivial a where
instance Trivial a where

class Category k hom | hom -> k where
    id :: (k a) => hom a a
    (.) :: hom b c -> hom a b -> hom a c
    subkind :: hom a b -> ((k a, k b) => r) -> r


-- Hask, haskell types and arrows
instance Category Trivial (->) where
    id = Prelude.id
    (.) = (Prelude..)
    subkind _ r = r

-- Endofunctors on Hask
type HaskFunctor = Prelude.Functor

data f :~>* g = (HaskFunctor f, HaskFunctor g) => HNT { getHNT :: forall a. f a -> g a }
infixl 1 %
(%) :: f :~>* g -> f a -> g a
(%) = getHNT

instance Category HaskFunctor (:~>*) where
    id = HNT id
    HNT g . HNT f = HNT (g . f)
    subkind (HNT _) r = r


-- Products

infix 5 &&&
class (Category k hom) => Products k hom p | hom -> p where
    (&&&) :: hom a b -> hom a c -> hom a (p b c)
    fst :: (k a, k b) => hom (p a b) a
    snd :: (k a, k b) => hom (p a b) b
    -- is subkindP necessary?
    subkindP :: (k a, k b) => Proxy (p a b) -> (k (p a b) => r) -> r

diag :: (Products k hom p, k a) => hom a (p a a)
diag = id &&& id

infix 5 ***
(***) :: (Products k hom p) => hom a a' -> hom b b' -> hom (p a b) (p a' b')
f *** g = (subkind f . subkind g) ((f . fst) &&& (g . snd))

instance Products Trivial (->) (,) where
    f &&& g = \x -> (f x, g x)
    fst (x,_) = x
    snd (_,y) = y
    subkindP _ r = r


data (f :*: g) x = Pair (f x) (g x)
deriving instance (HaskFunctor f, HaskFunctor g) => HaskFunctor (f :*: g)

instance Products HaskFunctor (:~>*) (:*:) where
    HNT f &&& HNT g = HNT (\x -> Pair (f x) (g x))
    fst = HNT $ \(Pair x _) -> x
    snd = HNT $ \(Pair _ y) -> y
    subkindP _ r = r



