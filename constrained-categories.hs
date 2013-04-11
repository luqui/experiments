{-# LANGUAGE PolyKinds, ConstraintKinds, TypeOperators, TypeFamilies, FlexibleInstances, ScopedTypeVariables, FlexibleContexts, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances, RankNTypes #-}

import Prelude hiding ((.), id, Functor(..), fst, snd, ($), return)
import qualified Prelude
import Data.Constraint (Constraint, (:-), (\\))
import qualified Data.Constraint as C
import qualified Data.Set as Set

data Proxy a = Proxy

class Trivial a where
instance Trivial a where

class (c a, d a) => AndC c d a where
instance (c a, d a) => AndC c d a where

type a ∈ hom = Obj hom a

class Category (hom :: k -> k -> *) where
    type Obj hom :: k -> Constraint
    type Obj hom = Trivial

    id :: (a ∈ hom) => hom a a
    (.) :: (a ∈ hom, b ∈ hom, c ∈ hom) => hom b c -> hom a b -> hom a c

class Functor c d (f :: k1 -> k2) | f -> c d where
    fobj :: (a ∈ c) :- (f a ∈ d)
    fmap :: (a ∈ c, b ∈ c) => c a b -> d (f a) (f b)

class (Category hom) => Products (hom :: k -> k -> *) where
    type Product hom :: k -> k -> k

    pobj :: (a ∈ hom, b ∈ hom) :- (Product hom a b ∈ hom)
    
    (&&&) :: (a ∈ hom, b ∈ hom, c ∈ hom) 
          => hom a b -> hom a c -> hom a (Product hom b c)
    fst :: (a ∈ hom, b ∈ hom) => hom (Product hom a b) a
    snd :: (a ∈ hom, b ∈ hom) => hom (Product hom a b) b

(|||) :: forall hom a b c d. (Products hom, a ∈ hom, b ∈ hom, c ∈ hom, d ∈ hom)
      => hom a b -> hom c d -> hom (Product hom a c) (Product hom b d)
f ||| g = ((f . fst) &&& (g . snd)) \\ (pobj :: (a ∈ hom, c ∈ hom) :- (Product hom a c ∈ hom))
                                    \\ (pobj :: (b ∈ hom, d ∈ hom) :- (Product hom b d ∈ hom))


class (Category c, Category d) => Subcategory c d | c -> d where
    embed :: (a ∈ c, b ∈ c, a ∈ d, b ∈ d) => c a b -> d a b

($) :: (Subcategory c (->)) => (a ∈ c, b ∈ c) => c a b -> a -> b
($) = embed


newtype NT c d f g = NT { getNT :: forall x. (x ∈ c) => d (f x) (g x) }


instance (Category c, Category d) => Category (NT c d) where
    type Obj (NT c d) = Functor c d
    id = NT ntID
        where
        ntID :: forall f x. (Functor c d f, x ∈ c) => d (f x) (f x)
        ntID = id \\ (fobj :: (x ∈ c) :- (f x ∈ d))

    g . f = NT (ntCompose g f)
        where
        ntCompose :: forall f g h x.
                  (Functor c d f, Functor c d g, Functor c d h, x ∈ c)
                  => NT c d g h -> NT c d f g -> d (f x) (h x)
        ntCompose g f = (getNT g . getNT f) \\ (fobj :: (x ∈ c) :- (f x ∈ d))
                                            \\ (fobj :: (x ∈ c) :- (g x ∈ d))
                                            \\ (fobj :: (x ∈ c) :- (h x ∈ d))


class (Category hom, Functor hom hom t) => Monad hom t where
    return :: (a ∈ hom) => hom a (t a)
    join :: (a ∈ hom) => hom (t (t a)) (t a)


instance Category (->) where
    type Obj (->) = Trivial
    id x = x
    (g . f) x = g (f x)


instance Functor (->) (->) Maybe where
    fobj = C.Sub C.Dict
    fmap f Nothing = Nothing
    fmap f (Just x) = Just (f x)

instance Functor (->) (->) [] where
    fobj = C.Sub C.Dict
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
    fobj = C.Sub C.Dict
    fmap f = Sub (Set.map (f $))

