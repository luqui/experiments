module goodstein where

import Level as L
open import Data.Nat
open import Data.Product
open import Relation.Binary.Product.StrictLex using (_×-strictTotalOrder_)

module dlist (A : Set) (_<_ : A -> A -> Set) where
  data DList : A -> Set where
    nil  : {y : A} -> DList y
    cons : {y : A} -> (x : A) -> (x < y) -> DList x -> DList y

Relation : Set -> Set₁
Relation A = A -> A -> Set

