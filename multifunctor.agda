module multifunctor where

import Level as L
open import Data.Fin
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality


data ⊤ {l} : Set l where
  tt : ⊤


tuple : forall {l} -> ℕ -> Set l -> Set (L.suc l)
tuple {l} zero _ = ⊤
tuple (suc n) A = A × tuple n A 


-- inj 1 0 = \X (Y) -> (X,Y)
-- inj 1 1 = \X (Y) -> (Y,X)

-- inj 2 0 = \X (Y,Z) -> (X,Y,Z)
-- inj 2 1 = \X (Y,Z) -> (Y,X,Z)
-- inj 2 2 = \X (Y,Z) -> (Y,Z,X)

inj : (n : ℕ) -> (i : Fin (suc n)) -> {l : L.Level} {A : Set l} -> A × tuple n A -> tuple (suc n) A
inj zero zero (X , tt) = (X , tt)
inj zero (suc ()) _
inj (suc n) zero (X , T) = (X , T)
inj (suc n) (suc i) (X , (A , T)) = (A , inj n i (X , T))


-- outj 1 0 = \(X) -> (X, ())
-- outj 2 0 = \(X,Y) -> (X, (Y))
-- outj 2 1 = \(X,Y) -> (Y, (X))

outj : (n : ℕ) -> (i : Fin (suc n)) -> {l : L.Level} {A : Set l} -> tuple (suc n) A -> A × tuple n A
outj n zero (X , Y) = (X , Y)
outj zero (suc ()) _
outj (suc n) (suc i) (A , Y) with outj n i Y
...                             | (X , Y′) = (X , (A , Y′))



inj-outj-inverses : (n : ℕ) (i : Fin (suc n)) {l : L.Level} {A : Set l} (t : tuple (suc n) A) -> inj n i (outj n i t) ≡ t
inj-outj-inverses zero zero (X , tt) = refl
inj-outj-inverses zero (suc ()) _
inj-outj-inverses (suc n) zero (X , Y) = refl
inj-outj-inverses (suc n) (suc i) (X , Y) with inj-outj-inverses n i Y
...                                          | refl = refl