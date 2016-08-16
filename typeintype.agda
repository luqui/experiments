{-# OPTIONS --type-in-type #-}

{- Set : Set is enough to create russell's paradox -}

module typeintype where

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Bool

data Type : Set where
  mkType : (A : Set) -> A -> Type

transport : {A B : Set} -> A ≡ B -> A -> B
transport refl x = x

record CompMember (A : Set) (a : A) (t : Type) : Set where
  field
    a-comprehension-type : A ≡ (Type -> Set)
    t-in-a : transport a-comprehension-type a t

selfMember : Type -> Set
selfMember (mkType A a) = CompMember A a (mkType A a)

notSelfMember : Type -> Set
notSelfMember t = ¬ (selfMember t)

russell : Type
russell = mkType (Type -> Set) notSelfMember

russell-q-1 : selfMember russell -> ¬ (selfMember russell) 
russell-q-1 record { a-comprehension-type = refl ; t-in-a = t-in-a } t = t-in-a t

russell-q-2 : ¬ (selfMember russell) -> selfMember russell
russell-q-2 f = record { a-comprehension-type = refl ; t-in-a = f }

implyFalsity : {A : Set} -> (A -> ¬ A) -> ¬ A
implyFalsity f a = f a a

paradox : ⊥
paradox = implyFalsity russell-q-1 (russell-q-2 (implyFalsity russell-q-1))

