{-# OPTIONS --type-in-type #-}

-- Exploring the free theorems and church numerals.
-- The key result is that the following are equivalent:
--    - The type (X : Set) -> (X -> X) -> X -> X represents the church numerals exactly
--    - The free theorem for this type is true

module reltype where

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Bool using (Bool ; true ; false)
open import Data.Nat
open import Data.Product
import Level
open import Relation.Binary.PropositionalEquality

Rel : Set -> Set -> Set
Rel X Y = X -> Y -> Set

Discrete : {A : Set} -> Rel A A
Discrete x y = x ≡ y

_~>_ : {A A' B B' : Set} -> Rel A A' -> Rel B B' -> Rel (A -> B) (A' -> B')
(R ~> R') f g = ∀ x y -> R x y -> R' (f x) (g y)

Π : {A : Set} -> (A -> Set) -> Set
Π {A} F = (x : A) -> F x

Λ : {F F' : Set -> Set} -> ({A A' : Set} -> Rel A A' -> Rel (F A) (F' A')) -> Rel (Π F) (Π F')
Λ F f g = {A A' : Set} (R : Rel A A') -> F R (f A) (g A')

FreeTheorem : {A : Set} -> Rel A A -> Set
FreeTheorem R = ∀ f -> R f f


-- Warm up: the only function of type (X : Set) -> X -> X  is the identity.
poly-id-theorem : FreeTheorem (Λ (\X -> X ~> X)) -> (f : (A : Set) -> A -> A) (A : Set) (x : A) -> f A x ≡ x
poly-id-theorem thm f A x = thm f (\y _ -> y ≡ x) x x refl


-- Now let's do church numerals.

ChurchNum : Set
ChurchNum = (X : Set) -> (X -> X) -> (X -> X)

-- This is just for reference, and better variable names.  FreeTheorem, as we see below, takes care of generating it.
ChurchNumTheorem : Set
ChurchNumTheorem = (f : ChurchNum)
                -> {A B : Set} (R : A -> B -> Set)
                -> (μ : A -> A) (ν : B -> B)
                -> ((x : A) (y : B) -> R x y -> R (μ x) (ν y))
                -> (x : A) (y : B) -> R x y -> R (f A μ x) (f B ν y)

church-num-theorem-verify : ChurchNumTheorem ≡ FreeTheorem (Λ (\X -> (X ~> X) ~> (X ~> X)))
church-num-theorem-verify = refl

-- Specializing to a unary relation ("induction") is also helpful.
ChurchNumTheoremSimple : Set
ChurchNumTheoremSimple = (f : ChurchNum)
                         {A : Set} (R : A -> Set)
                         (μ : A -> A) ->
                         ((x : A) -> R x -> R (μ x)) ->
                         (x : A) -> R x -> R (f A μ x)

fpow : {A : Set} -> ℕ -> (A -> A) -> (A -> A)
fpow zero _ x = x
fpow (suc n) f x = f (fpow n f x)

fpow-nat : (n : ℕ) -> fpow n suc zero ≡ n
fpow-nat zero = refl
fpow-nat (suc n) = cong suc (fpow-nat n)

record Orbit {A : Set} (μ : A -> A) (x0 : A) (y : A) : Set where
  field
    n : ℕ
    orbit : y ≡ fpow n μ x0

-- Here we show that the church numerals are exactly finite repeated applications of a function.
module ChurchNums (freethm : ChurchNumTheorem) (f : ChurchNum) where
  simplethm : ChurchNumTheoremSimple
  simplethm f R μ ind x rx = freethm f (\x tt -> R x) μ (\t -> t) (\x _ r -> ind x r) x tt rx

  generalization : (n : ℕ) -> f ℕ suc zero ≡ n
                -> {A : Set} (μ : A -> A) (x0 : A)
                -> f A μ x0 ≡ fpow n μ x0
  generalization n p μ x0 = 
    let r = freethm f (\a n' -> a ≡ fpow n' μ x0) μ suc (\x y -> cong μ) x0 zero refl 
    in subst (\ □ -> f _ μ x0 ≡ fpow □ μ x0) p r

  find-orbit : {A : Set} (μ : A -> A)
            -> (x0 : A) -> Orbit μ x0 (f A μ x0)
  find-orbit {A} μ x0 = simplethm f (Orbit μ x0) μ ind x0 basecase
    where
    basecase = record { n = zero ; orbit = refl }
    ind : (x : A) -> Orbit μ x0 x -> Orbit μ x0 (μ x)
    ind x orb = record { n = suc (Orbit.n orb) ; orbit = cong μ (Orbit.orbit orb) }

  characterization : Extensionality Level.zero Level.zero
                  -> Σ ℕ (\n -> f ≡ (\X -> fpow n))
  characterization ex =
    let orb = find-orbit suc zero
    in Orbit.n orb , ex (\X -> ex (\μ -> ex (\x0 -> generalization (Orbit.n orb) (trans (Orbit.orbit orb) (fpow-nat _)) μ x0)))

-- And here we show that this characterization is sufficient to have the free theorem, establishing equivalence.
reverse-characterization : ((f : ChurchNum) -> Σ ℕ (\n -> f ≡ (\X -> fpow n))) -> ChurchNumTheorem
reverse-characterization char f R μ ν ind x y r0 
      with char f
...      | n , p rewrite p = fpow-induction n
  where
  fpow-induction : (n : ℕ) -> R (fpow n μ x) (fpow n ν y)
  fpow-induction zero = r0
  fpow-induction (suc n) = ind _ _ (fpow-induction n)
