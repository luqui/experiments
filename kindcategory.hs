{-# LANGUAGE RankNTypes, TypeInType, TypeFamilies, TypeOperators, TypeSynonymInstances, FlexibleInstances, GADTs #-}

import Prelude hiding (id, (.))
import Data.Kind (Type)

-- f ~> g = forall x. f x ~> g x

class Cat k where
    type Hom k :: k -> k -> Type
    id :: Hom k a a
    (.) :: Hom k b c -> Hom k a b -> Hom k a c

type (a :: k) ~> (b :: k) = Hom k a b

infixl 8 %
data NT (f :: a -> b) (g :: a -> b)
    = NT { (%) :: forall x. Hom b (f x) (g x) }

instance Cat Type where
    type Hom Type = (->)
    id x = x
    (g . f) x = g (f x)

instance (Cat b) => Cat (a -> b) where
    type Hom (a -> b) = NT
    id = NT id
    NT g . NT f = NT (g . f)

newtype Discrete k = Discrete k

data a == b where
    Refl :: a == a

instance Cat (Discrete k) where
    type Hom (Discrete k) = (==)
    id = Refl
    Refl . b = b

maybeToList :: Maybe ~> []
maybeToList = NT (maybe [] (:[]))
