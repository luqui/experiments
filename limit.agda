{-# OPTIONS --type-in-type #-}

module limit where

import Level as L

Functor : Set
Functor = Set -> Set

NatTrans : Functor -> Functor -> Set
NatTrans f g = {a : Set} -> f a -> g a

record NatIso (f g : Functor) : Set where
  field
    forward : NatTrans f g
    backward : NatTrans g f 

Const : Set -> Functor
Const b a = b

Cone : Functor -> Set -> Set
Cone d v = NatTrans (Const v) d

Limit : Functor -> Set -> Set
Limit d u = NatIso (Cone d) (\v -> v -> u)


data ProdL (a b : Set) : Set -> Set where
  Fst : a -> ProdL a b a
  Snd : b -> ProdL a b b

data Product (a b : Set) : Set where
  pair : a -> b -> Product a b

data Unit : Set where
  unit : Unit

proj1 : {a b : Set} -> Product a b -> a
proj1 (pair x _) = x

proj2 : {a b : Set} -> Product a b -> b
proj2 (pair _ y) = y

proj1L : {a b : Set} -> ProdL a b a -> a
proj1L (Fst x) = x
proj1L (Snd y) = y

proj2L : {a b : Set} -> ProdL a b b -> b
proj2L (Fst x) = x
proj2L (Snd y) = y

prodToPair : {a b : Set} -> ({c : Set} -> ProdL a b c) -> Product a b
prodToPair {a} {b} f = pair (proj1L (f {a})) (proj2L (f {b}))


prodLimit : (a b : Set) -> Limit (ProdL a b) (Product a b)
prodLimit a b = record {
          forward = \f x -> prodToPair {a} {b} (\{c} -> f {c} x) ;
          backward = \f x -> {!!}
  } 
