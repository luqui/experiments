module Fin-inj where

import Level
open Level using (Level)

open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Core using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl) 
open import Relation.Nullary.Core using (¬_)
open import Function using (_∘_)


ap : {l : Level} {A B : Set l} -> A ≡ B -> A -> B
ap = Eq.subst (\X -> X)

sym-equal : {l : Level} {A : Set l} {x y : A} -> x ≡ y -> y ≡ x
sym-equal = IsEquivalence.sym Eq.isEquivalence

infixl 9 _•_
_•_ : {l : Level} {A : Set l} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
_•_ = IsEquivalence.trans Eq.isEquivalence

zero-not-suc : {n :  ℕ} -> ℕ.zero ≡ ℕ.suc n -> ⊥
zero-not-suc ()

ℕ-suc-inj : {m n : ℕ} -> ℕ.suc m ≡ ℕ.suc n -> m ≡ n
ℕ-suc-inj refl = refl

MereProp : {l : Level} -> Set l -> Set l
MereProp S = (A B : S) -> A ≡ B

record Bijection (X Y : Set) : Set where
  field
    ⟶ : X -> Y
    ⟵ : Y -> X
    inv₁ : {x : X} -> ⟵ (⟶ x) ≡ x
    inv₂ : {y : Y} -> y ≡ ⟶ (⟵ y)

identity-bijection : {X : Set} -> Bijection X X
identity-bijection = record { ⟶ = \x -> x ; ⟵ = \x -> x ; inv₁ = refl ; inv₂ = refl }

equality-bijection : {X Y : Set} -> X ≡ Y -> Bijection X Y
equality-bijection refl = identity-bijection 

sym-bijection : {X Y : Set} -> Bijection X Y -> Bijection Y X
sym-bijection bij = record {
    ⟶ = Bijection.⟵ bij ;
    ⟵ = Bijection.⟶ bij ;
    inv₁ = sym-equal (Bijection.inv₂ bij) ;
    inv₂ = sym-equal (Bijection.inv₁ bij)
  }

Bijection-mere-prop : {X Y : Set} -> Bijection X Y -> MereProp X -> MereProp Y
Bijection-mere-prop bij mp a b = let q = mp (Bijection.⟵ bij a) (Bijection.⟵ bij b)
                                     r = Eq.cong (Bijection.⟶ bij) q
                                  in Bijection.inv₂ bij • r • sym-equal (Bijection.inv₂ bij)

bijection-inj : {X Y : Set} {a b : X} -> (bij : Bijection X Y) -> Bijection.⟶ bij a ≡ Bijection.⟶ bij b -> a ≡ b
bijection-inj bij p = sym-equal (Bijection.inv₁ bij) • Eq.cong (Bijection.⟵ bij) p • Bijection.inv₁ bij

infixl 9 _∘-bij_
_∘-bij_ : {X Y Z : Set} -> Bijection Y Z -> Bijection X Y -> Bijection X Z
_∘-bij_ bij bij' = record {
      ⟶ = Bijection.⟶ bij ∘ Bijection.⟶ bij' ;
      ⟵ = Bijection.⟵ bij' ∘ Bijection.⟵ bij ;
      inv₁ = Eq.cong (Bijection.⟵ bij') (Bijection.inv₁ bij) • Bijection.inv₁ bij' ;
      inv₂ = Bijection.inv₂ bij • Eq.cong (Bijection.⟶ bij) (Bijection.inv₂ bij') 
  }

Fin-one-mere-prop : MereProp (Fin (suc zero))
Fin-one-mere-prop zero zero = refl
Fin-one-mere-prop _ (suc ())
Fin-one-mere-prop (suc ()) zero

zero-not-suc-Fin : {n : ℕ} {a : Fin (suc n)} -> ¬ (Fin.zero ≡ Fin.suc a)
zero-not-suc-Fin ()

Fin-suc-inj : {n : ℕ} {a b : Fin n} -> Fin.suc a ≡ Fin.suc b -> a ≡ b
Fin-suc-inj refl = refl


skip-Fin : {n : ℕ} -> Fin (suc (suc n)) -> Fin (suc (suc n)) -> Fin (suc n)
skip-Fin zero zero = zero
skip-Fin zero (suc a) = a
skip-Fin (suc p) zero = zero
skip-Fin {zero} p a = zero
skip-Fin {suc n} (suc p) (suc a) = suc (skip-Fin p a)

skip-Fin-zero-suc : {n : ℕ} {x : Fin (suc n)} -> skip-Fin zero (suc x) ≡ x
skip-Fin-zero-suc {zero} {zero} = refl
skip-Fin-zero-suc {zero} {suc ()}
skip-Fin-zero-suc {suc n} {x} = refl

suc-skip-Fin-zero : {n : ℕ} {x : Fin (suc (suc n))} -> ¬ (x ≡ zero) -> suc (skip-Fin zero x) ≡ x
suc-skip-Fin-zero {n} {zero} p = ⊥-elim (p refl)
suc-skip-Fin-zero {n} {suc x} p = refl

unskip-Fin : {n : ℕ} -> Fin (suc (suc n)) -> Fin (suc n) -> Fin (suc (suc n))
unskip-Fin {zero} zero a = suc zero
unskip-Fin {zero} (suc _) a = zero  -- complete the enumeration?
unskip-Fin {suc n} zero a = suc a
unskip-Fin {suc n} (suc p) zero = zero
unskip-Fin {suc n} (suc p) (suc a) = suc (unskip-Fin p a)

skip-unskip-equal : {n : ℕ} (p : Fin (suc (suc n))) {x : Fin (suc n)} -> skip-Fin p (unskip-Fin p x) ≡ x
skip-unskip-equal {zero} zero {zero} = refl
skip-unskip-equal {zero} (suc p) {zero} = refl
skip-unskip-equal {zero} p {suc ()}
skip-unskip-equal {suc n} zero {x} = refl
skip-unskip-equal {suc n} (suc p) {zero} = refl
skip-unskip-equal {suc n} (suc p) {suc x} = Eq.cong suc (skip-unskip-equal p)

unskip-skip-equal : {n : ℕ} (p : Fin (suc (suc n))) (x : Fin (suc (suc n))) -> ¬ (p ≡ x) -> unskip-Fin p (skip-Fin p x) ≡ x
unskip-skip-equal {zero} zero zero pt = ⊥-elim (pt refl)
unskip-skip-equal {zero} zero (suc zero) pt = refl
unskip-skip-equal {zero} zero (suc (suc ())) pt
unskip-skip-equal {zero} (suc p) zero pt = refl
unskip-skip-equal {zero} (suc zero) (suc zero) pt = ⊥-elim (pt refl)
unskip-skip-equal {zero} (suc (suc ())) (suc zero) pt
unskip-skip-equal {zero} (suc p) (suc (suc ())) pt
unskip-skip-equal {suc n} zero zero pt = ⊥-elim (pt refl)
unskip-skip-equal {suc n} zero (suc x) pt = refl
unskip-skip-equal {suc n} (suc p) zero pt = refl
unskip-skip-equal {suc n} (suc p) (suc x) pt = Eq.cong suc (unskip-skip-equal p x (pt ∘ Eq.cong suc))

unskip-pivot-not-equal : {n : ℕ} -> (p : Fin (suc (suc n))) (x : Fin (suc n)) -> ¬ (unskip-Fin p x ≡ p)
unskip-pivot-not-equal {zero} zero x ()
unskip-pivot-not-equal {zero} (suc p) x ()
unskip-pivot-not-equal {suc n} zero x ()
unskip-pivot-not-equal {suc n} (suc p) zero ()
unskip-pivot-not-equal {suc n} (suc p) (suc x) pf = unskip-pivot-not-equal p x (Fin-suc-inj pf)


swizzle : {m n : ℕ} -> Bijection (Fin (suc (suc m))) (Fin (suc (suc n))) -> Bijection (Fin (suc m)) (Fin (suc n))
swizzle bij =
  let pivot = Bijection.⟶ bij zero in
  record {
    ⟶ = skip-Fin pivot ∘ Bijection.⟶ bij ∘ suc ;
    ⟵ = skip-Fin zero ∘ Bijection.⟵ bij ∘ unskip-Fin pivot ;
    inv₁ = \{x} -> let bij-one-not-pivot : ¬ (Bijection.⟶ bij (suc x) ≡ pivot)
                       bij-one-not-pivot = zero-not-suc-Fin ∘ sym-equal ∘ bijection-inj bij
                       x' = Bijection.⟶ bij (suc x)
                   in Eq.cong (skip-Fin zero ∘ Bijection.⟵ bij) (unskip-skip-equal pivot x' (bij-one-not-pivot ∘ sym-equal)) 
                     • Eq.cong (skip-Fin zero) (Bijection.inv₁ bij)
                     • skip-Fin-zero-suc ;
    inv₂ = \{x} -> let bij-unskip-pivot-not-zero : ¬ (Bijection.⟵ bij (unskip-Fin pivot x) ≡ zero)
                       bij-unskip-pivot-not-zero p = unskip-pivot-not-equal pivot x (Bijection.inv₂ bij • Eq.cong (Bijection.⟶ bij) p)
                   in Eq.subst (\ [] -> x ≡ skip-Fin pivot (Bijection.⟶ bij [])) (sym-equal (suc-skip-Fin-zero bij-unskip-pivot-not-zero))
                     (Eq.subst (\ [] -> x ≡ skip-Fin pivot []) (Bijection.inv₂ bij) 
                      (sym-equal (skip-unskip-equal pivot)))
  }

Fin-no-bijection-zero : {n : ℕ} -> ¬ (Bijection (Fin zero) (Fin (suc n)))
Fin-no-bijection-zero bij with Bijection.⟵ bij zero
...                          | ()

Fin-no-bijection-one : {n : ℕ} -> ¬ (Bijection (Fin (suc zero)) (Fin (suc (suc n))))
Fin-no-bijection-one bij = zero-not-suc-Fin (Fin-two-mere-prop zero (suc zero))
  where
  Fin-two-mere-prop = Bijection-mere-prop bij Fin-one-mere-prop
  
  


Fin-downgrade : {m n : ℕ} -> Bijection (Fin (suc m)) (Fin (suc n)) -> Bijection (Fin m) (Fin n)
Fin-downgrade {zero} {zero} bij = identity-bijection
Fin-downgrade {zero} {suc n} bij = ⊥-elim (Fin-no-bijection-one bij)
Fin-downgrade {suc m} {zero} bij = ⊥-elim (Fin-no-bijection-one (sym-bijection bij))
Fin-downgrade {suc m} {suc n} bij = swizzle bij


Fin-no-bijection : {m n : ℕ} -> ¬ (m ≡ n) -> ¬ (Bijection (Fin m) (Fin n))
Fin-no-bijection {zero} {zero} p bij = ⊥-elim (p refl)
Fin-no-bijection {zero} {suc n} p bij with Bijection.⟵ bij zero
...                                       | ()
Fin-no-bijection {suc m} {zero} p bij with Bijection.⟶ bij zero
...                                       | ()
Fin-no-bijection {suc m} {suc n} p bij = 
  Fin-no-bijection {m} {n} (\p' -> p (Eq.cong suc p')) (Fin-downgrade bij)




Fin-injection : {m n : ℕ} -> Bijection (Fin m) (Fin n) -> m ≡ n
Fin-injection {zero} {zero} = \_ -> refl
Fin-injection {zero} {suc n} = ⊥-elim ∘ Fin-no-bijection zero-not-suc
Fin-injection {suc m} {zero} = ⊥-elim ∘ Fin-no-bijection (zero-not-suc ∘ sym-equal)
Fin-injection {suc m} {suc n} = Eq.cong suc ∘ Fin-injection ∘ Fin-downgrade

Fin-injective : {m n : ℕ} -> Fin m ≡ Fin n -> m ≡ n
Fin-injective p = Fin-injection (equality-bijection p)
