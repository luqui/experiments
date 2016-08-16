{-# OPTIONS --type-in-type #-}

{- Set : Set is enough to create russell's paradox -}

module typeintype where

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool

data Value : Set where
  mkValue : (A : Set) -> A -> Value

valType : Value -> Set
valType (mkValue t _) = t

valValue : (v : Value) -> valType v
valValue (mkValue _ v) = v

transport : {A B : Set} -> A ≡ B -> A -> B
transport refl x = x

-- "v ∈ s" encodes the predicate that s is a set-comprehension-style value
-- (i.e. Value -> Set) and that it contains v.  If s is any other kind of value, 
-- this is uninhabited.
record _∈_ (v : Value) (s : Value) : Set where
  field
    a-comprehension : valType s ≡ (Value -> Set)
    t-in-a : transport a-comprehension (valValue s) v

selfMember : Value -> Set
selfMember t = t ∈ t

russell : Value
russell = mkValue (Value -> Set) (\t -> ¬ (selfMember t))

russell-q-1 : selfMember russell -> ¬ (selfMember russell) 
russell-q-1 record { a-comprehension = refl ; t-in-a = t-in-a } t = t-in-a t

russell-q-2 : ¬ (selfMember russell) -> selfMember russell
russell-q-2 f = record { a-comprehension = refl ; t-in-a = f }

implyFalsity : {A : Set} -> (A -> ¬ A) -> ¬ A
implyFalsity f a = f a a

paradox : ⊥
paradox = implyFalsity russell-q-1 (russell-q-2 (implyFalsity russell-q-1))

