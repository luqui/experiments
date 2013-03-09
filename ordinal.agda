module ordinal where

import Level as L
open import Data.Nat using (ℕ)
open import Function using (case_of_)


data Ordinal l : Set (L.suc l) where
  lub : (A : Set l) -> (A -> Ordinal l) -> Ordinal l

data Σ {l} (A : Set l) (f : A -> Set l) : Set l where
  sig : (x : A) -> f x -> Σ A f

data False {l} : Set l where

data True {l} : Set l where
  tt : True

¬_ : forall {l} -> Set l -> Set l
¬_ {l} p = p -> False {l}

_≤_ : forall {l} -> Ordinal l -> Ordinal l -> Set l
lub A f ≤ lub B g = (x : A) -> Σ B (\y -> f x ≤ g y)

thm-le-refl : forall {l} (α : Ordinal l) -> α ≤ α
thm-le-refl (lub A f) = \x -> sig x (thm-le-refl (f x))

thm-le-trans : forall {l} {α β γ : Ordinal l} -> α ≤ β -> β ≤ γ -> α ≤ γ 
thm-le-trans {_} {lub A f} {lub B g} {lub C h} alb blg =
  \x -> case alb x of \{(sig y l) -> 
        case blg y of \{(sig z l′) -> 
        sig z (thm-le-trans l l′)}}

_<_ : forall {l} -> Ordinal l -> Ordinal l -> Set l
α < lub B g = Σ B (\y -> α ≤ g y)

thm-lub-le : forall {l} {A : Set l} {f} -> (x : A) -> f x ≤ lub A f
thm-lub-le {_} {_} {f} x with f x         | thm-le-refl (f x)
...                         | lub fxA fxf | refl = 
            \fxx -> sig x {!!} 

thm-lt-implies-le : forall {l} {α β : Ordinal l} -> α < β -> α ≤ β
thm-lt-implies-le {_} {lub A f} {lub B g} alb = 
  \x -> case alb of \{(sig y l) -> sig y {!!}}


zero : forall {l} -> Ordinal l
zero = lub False \{()}

thm-zero-le-all : forall {l} (α : Ordinal l) -> zero ≤ α
thm-zero-le-all (lub _ _) = \{()}

suc : forall {l} -> Ordinal l -> Ordinal l
suc α = lub True \{tt -> α}

thm-le-suc : forall {l} -> (α : Ordinal l) -> α ≤ suc α
thm-le-suc (lub A f) = \x -> {!!}