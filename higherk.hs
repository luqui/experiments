{-# OPTIONS -fdefer-type-errors #-}
{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies, TypeOperators, RankNTypes, GADTs, TypeApplications, ScopedTypeVariables, UndecidableInstances, MultiParamTypeClasses, TypeInType, TypeSynonymInstances, FlexibleInstances, InstanceSigs #-}

import Data.Kind (Type)
import Unsafe.Coerce
import Data.Type.Equality

type family (~>) :: k -> k -> Type
type instance (~>) = (->)
newtype NT a b = NT { applyNT :: forall x. a x ~> b x }
type instance (~>) = NT

left :: (,) ~> Either
left = NT (NT (Left . fst))

type family Promote2 :: (j -> k -> l) -> (a -> j) -> (a -> k) -> (a -> l) where

promote2_law :: forall f x y z. f (x z) (y z) :~: Promote2 f x y z
promote2_law = unsafeCoerce Refl

data Proxy a = Proxy

class Products k where
    type (:*:) :: k -> k -> k
    fstP :: forall (a :: k) (b :: k). (a :*: b) ~> a
    sndP :: forall (a :: k) (b :: k). (a :*: b) ~> b
    pair :: forall (a :: k) (b :: k) (c :: k). (a ~> b) -> (a ~> c) -> (a ~> (b :*: c))
    
instance Products Type where
    type (:*:) = (,)
    fstP = fst
    sndP = snd
    pair f g x = (f x, g x)

instance (Products k) => Products (j -> k) where
    type (:*:) = Promote2 (:*:)
    fstP = NT fstP1
    sndP = NT sndP1
    pair f g = NT (pair1 f g)

infixl 9 ~%
(~%) = apply

fstP1 :: forall (a :: j -> k) (b :: j -> k) (x :: j). Products k => (a :*: b) x ~> a x
fstP1 = castWith (Refl ~% promote2_law @(:*:) @a @b @x ~% Refl) fstP

sndP1 :: forall (a :: j -> k) (b :: j -> k) (x :: j). Products k => (a :*: b) x ~> b x
sndP1 = castWith (Refl ~% promote2_law @(:*:) @a @b @x ~% Refl) sndP

pair1 :: forall (a :: j -> k) (b :: j -> k) (c :: j -> k) (x :: j). Products k => 
         (a ~> b) -> (a ~> c) -> a x ~> (b :*: c) x
pair1 f g = castWith (Refl ~% Refl ~% promote2_law @(:*:) @b @c @x) (pair (applyNT f) (applyNT g))

