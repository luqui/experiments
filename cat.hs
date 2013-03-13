{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, GADTs, FlexibleContexts, ConstraintKinds, PolyKinds, KindSignatures, DataKinds, ScopedTypeVariables, RankNTypes #-}

import qualified Prelude
import Prelude hiding ((.), id, Functor, fmap, Monad, return, (>>=), (=<<))
import GHC.Prim (Constraint)
import qualified Data.Set as Set


class Category c where
    id  :: c x x
    (.) :: c y z -> c x y -> c x z

type Hask = (->)

instance Category Hask where
    id = Prelude.id
    (.) = (Prelude..)


class (Category c, Category d) => Functor c d f where
    fmap :: c a b -> d (f a) (f b)


instance (Prelude.Functor f) => Functor Hask Hask f where
    fmap = Prelude.fmap


data Iso a b = Iso { action :: a -> b, inverse :: b -> a }

instance Category Iso where
    id = Iso id id
    Iso g g' . Iso f f' = Iso (g . f) (f' . g')

data Endo a = Endo { getEndo :: a -> a }

instance Functor Iso Hask Endo where
    fmap (Iso f f') (Endo t) = Endo (f . t . f')


data Discrete a b where
    Refl :: Discrete a a

instance Category Discrete where
    id = Refl
    Refl . Refl = Refl


type EndoFunctor c f = Functor c c f

class (EndoFunctor c t) => Monad c t where
    return :: c a (t a)
    join :: c (t (t a)) (t a)

extend :: (Monad c t) => c a (t b) -> c (t a) (t b)
extend f = join . fmap f


newtype Hom (c :: * -> Constraint) a b = Hom (a -> b)

instance Category (Hom c) where
    id = Hom id
    Hom g . Hom f = Hom (g . f)

instance Functor (Hom Ord) Hask Set.Set where
    fmap (Hom f) = Set.mapMonotonic f

instance Functor (Hom Ord) (Hom Ord) Set.Set where
    fmap (Hom f) = Hom (Set.mapMonotonic f)

data Dict c a where
    Dict :: c a => Dict c a

newtype CImpl c c' = CImpl (forall a. Dict c a -> Dict c' a)

instance Category CImpl where
    id = CImpl id
    CImpl g . CImpl f = CImpl (g . f)

newtype Impl c a b = Impl (Dict c a -> Dict c b)

instance Category (Impl c) where
    id = Impl id
    Impl g . Impl f = Impl (g . f)


data Product c d a b = Product (c a b) (d a b)

instance (Category c, Category d) => Category (Product c d) where
    id = Product id id
    Product g g' . Product f f' = Product (g . f) (g' . f')

newtype FCat f a b = FCat (f a -> f b)

instance Category (FCat f) where
    id = FCat id
    FCat g . FCat f = FCat (g . f)

instance Functor (FCat f) Hask f where
    fmap (FCat f) = f




