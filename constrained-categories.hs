{-# LANGUAGE PolyKinds, ConstraintKinds, TypeOperators, TypeFamilies, FlexibleInstances, ScopedTypeVariables, FlexibleContexts, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances, RankNTypes #-}

import Prelude hiding ((.), id, Functor(..), fst, snd, ($), return)
import qualified Prelude
import GHC.Prim (Constraint)
import qualified Data.Set as Set

class Trivial a where
instance Trivial a where

class (c a, d a) => AndC c d a where
instance (c a, d a) => AndC c d a where

type a ∈ hom = Obj hom a

class Category (hom :: k -> k -> *) where
    type Obj hom :: k -> Constraint
    id :: (a ∈ hom) => hom a a
    (.) :: (a ∈ hom, b ∈ hom, c ∈ hom) => hom b c -> hom a b -> hom a c

class Functor c d (f :: k1 -> k2) | f -> c d where
    fmap :: (a ∈ c, b ∈ c, f a ∈ d, f b ∈ d) 
         => c a b -> d (f a) (f b)

class (Category hom) => Products (hom :: k -> k -> *) where
    type Product hom :: k -> k -> k
    (&&&) :: (a ∈ hom, b ∈ hom, c ∈ hom, Product hom b c ∈ hom) 
          => hom a b -> hom a c -> hom a (Product hom b c)
    fst :: (a ∈ hom, b ∈ hom, Product hom a b ∈ hom) => hom (Product hom a b) a
    snd :: (a ∈ hom, b ∈ hom, Product hom a b ∈ hom) => hom (Product hom a b) b

(|||) :: (Products hom, a ∈ hom, b ∈ hom, c ∈ hom, d ∈ hom, Product hom a c ∈ hom, Product hom b d ∈ hom)
      => hom a b -> hom c d -> hom (Product hom a c) (Product hom b d)
f ||| g = (f . fst) &&& (g . snd)


class (Category c, Category d) => Subcategory c d | c -> d where
    embed :: (a ∈ c, b ∈ c, a ∈ d, b ∈ d) => c a b -> d a b

($) :: (Subcategory c (->)) => (a ∈ c, b ∈ c) => c a b -> a -> b
($) = embed


newtype NT c d f g = NT { getNT :: forall x. (x ∈ c, f x ∈ d, g x ∈ d) => d (f x) (g x) }

instance (Category c, Category d) => Category (NT c d) where
    type Obj (NT c d) = Functor c d
    id = NT id
    NT g . NT f = NT (g . f)


class (Category hom, Functor hom hom t) => Monad hom t where
    return :: (a ∈ hom, t a ∈ hom) => hom a (t a)
    join :: (t (t a) ∈ hom, t a ∈ hom) => hom (t (t a)) (t a)


instance Category (->) where
    type Obj (->) = Trivial
    id x = x
    (g . f) x = g (f x)


instance Functor (->) (->) Maybe where
    fmap f Nothing = Nothing
    fmap f (Just x) = Just (f x)

instance Functor (->) (->) [] where
    fmap = map


instance Subcategory (->) (->) where
    embed = id


newtype Sub (hom :: k -> k -> *) (c :: k -> Constraint) a b = Sub { getSub :: hom a b }

instance (Category hom) => Category (Sub hom c) where
    type Obj (Sub hom c) = AndC c (Obj hom)
    id = Sub id
    Sub g . Sub f = Sub (g . f)

instance (Category hom) => Subcategory (Sub hom c) hom where
    embed (Sub f) = f


instance Functor (Sub (->) Ord) (Sub (->) Ord) Set.Set where
    fmap f = Sub (Set.map (f $))

