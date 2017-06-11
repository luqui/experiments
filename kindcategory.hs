{-# LANGUAGE RankNTypes, TypeInType, DataKinds, TypeFamilies, TypeOperators, TypeSynonymInstances, FlexibleInstances, GADTs #-}

import Prelude hiding (id, (.))
import Data.Kind (Type)
import Control.Monad ((<=<))

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

data a * b = Pair a b
type family Proj1 (p :: a * b) :: a where
    Proj1 (Pair x y) = x
type family Proj2 (p :: a * b) :: b where
    Proj2 (Pair x y) = y

newtype ArrPair k k' (f :: k * k') (g :: k * k') 
    = ArrPair { getArrPair :: (Hom k (Proj1 f) (Proj1 g)) * (Hom k' (Proj2 f) (Proj2 g)) }

instance (Cat k, Cat k') => Cat (k * k') where
    type Hom (k * k') = ArrPair k k'
    id = ArrPair (Pair id id)
    ArrPair (Pair g g') . ArrPair (Pair f f') = ArrPair (Pair (g . f) (g' . f'))

newtype Monadic m = M { getM :: Type }

type family GetM m (a :: Monadic m) :: Type where
    GetM m (M x) = x

newtype MonadHom m (a :: Monadic m) (b :: Monadic m) = MonadHom { getMonadHom :: GetM m a -> m (GetM m b) }

instance (Monad m) => Cat (Monadic m) where
    type Hom (Monadic m) = MonadHom m
    id = MonadHom return
    MonadHom g . MonadHom f = MonadHom (g <=< f)

maybeToList :: Maybe ~> []
maybeToList = NT (maybe [] (:[]))
