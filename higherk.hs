{-# OPTIONS -fdefer-type-errors #-}
{-# LANGUAGE DataKinds, PolyKinds, TypeFamilies, TypeOperators, RankNTypes, GADTs, TypeApplications, ScopedTypeVariables, UndecidableInstances, MultiParamTypeClasses, TypeInType, TypeSynonymInstances, FlexibleInstances, InstanceSigs, FlexibleContexts #-}

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Type)
import Unsafe.Coerce
import Data.Type.Equality

type family (~>) :: k -> k -> Type
type instance (~>) = (->)
newtype NT (a :: j -> k) (b :: j -> k) 
    = NT { applyNT :: forall x. a x ~> b x }
type instance (~>) = NT

instance (Category ((~>) :: k -> k -> Type)) => Category (NT :: (j -> k) -> (j -> k) -> Type) where
    id = NT id
    NT g . NT f = NT (g . f)

-- Example of higher-kinded natrual transformations.
left :: (,) ~> Either
left = NT (NT (Left . fst))

right :: (,) ~> Either
right = NT (NT (Right . snd))


-- An "axiomatic type"
type family Promote2 :: (j -> k -> l) -> (a -> j) -> (a -> k) -> (a -> l) where

promote2_law :: forall f x y z. f (x z) (y z) :~: Promote2 f x y z
promote2_law = unsafeCoerce Refl

-- Polykinded products!
class (Category ((~>) :: k -> k -> Type)) => Products k where
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

pair1 :: forall (a :: j -> k) (b :: j -> k) (c :: j -> k) (x :: j). 
         (Products k, Category ((~>) :: k -> k -> Type)) =>
         (a ~> b) -> (a ~> c) -> a x ~> (b :*: c) x
pair1 f g = castWith (Refl ~% Refl ~% promote2_law @(:*:) @b @c @x) (pair (applyNT f) (applyNT g))


example :: Either Int Int
example = applyNT (applyNT mor) (1,2)
    where
    mor :: (,) ~> Either
    mor = fstP . pair left right
