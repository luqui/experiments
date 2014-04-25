module wf where

import Level
open Level using (Level)

infixl 9 _∘_
_∘_ : {l : Level} {A B C : Set l} -> (B -> C) -> (A -> B) -> (A -> C)
(g ∘ f) x = g (f x)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : {A : Set} -> ⊥ -> A
absurd ()

¬_ : Set -> Set
¬_ X = X -> ⊥

data _*_ (X Y : Set) : Set where
  pair : X -> Y -> X * Y

data Σ (X : Set) (P : X -> Set) : Set where
  _∥_ : (x : X) -> P x -> Σ X P

data _≡_ {l} {A : Set l} (a : A) : A -> Set l where
  refl : a ≡ a

f-equal : {l m : Level} {A : Set l} {B : Set m} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
f-equal f refl = refl

ap : {l : Level} {A B : Set l} -> A ≡ B -> A -> B
ap refl X = X

sym-equal : {l : Level} {A : Set l} {x y : A} -> x ≡ y -> y ≡ x
sym-equal refl = refl 

path-ind : {l : Level} {A : Set l} (P : A -> Set l) {x y : A} -> x ≡ y -> P x -> P y
path-ind P refl X = X

infixl 9 _•_
_•_ : {l : Level} {A : Set l} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
refl • refl = refl

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

data _<_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero < succ n
  succ<succ : {m n : Nat} -> m < n -> succ m < succ n

<-mere-prop : {m n : Nat} -> (p q : m < n) -> p ≡ q
<-mere-prop zero<succ zero<succ = refl
<-mere-prop (succ<succ p) (succ<succ q) = f-equal succ<succ (<-mere-prop p q)

zero-not-succ : {n : Nat} -> ¬ (zero ≡ succ n)
zero-not-succ p = ap (f-equal family p) tt
  where
  family : Nat -> Set
  family zero = ⊤
  family (succ n) = ⊥ 

Nat-downgrade : {m n : Nat} -> succ m ≡ succ n -> m ≡ n
Nat-downgrade refl = refl

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
                                     r = f-equal (Bijection.⟶ bij) q
                                  in Bijection.inv₂ bij • r • sym-equal (Bijection.inv₂ bij)

bijection-inj : {X Y : Set} {a b : X} -> (bij : Bijection X Y) -> Bijection.⟶ bij a ≡ Bijection.⟶ bij b -> a ≡ b
bijection-inj bij p = sym-equal (Bijection.inv₁ bij) • f-equal (Bijection.⟵ bij) p • Bijection.inv₁ bij

infixl 9 _∘-bij_
_∘-bij_ : {X Y Z : Set} -> Bijection Y Z -> Bijection X Y -> Bijection X Z
_∘-bij_ bij bij' = record {
      ⟶ = Bijection.⟶ bij ∘ Bijection.⟶ bij' ;
      ⟵ = Bijection.⟵ bij' ∘ Bijection.⟵ bij ;
      inv₁ = f-equal (Bijection.⟵ bij') (Bijection.inv₁ bij) • Bijection.inv₁ bij' ;
      inv₂ = Bijection.inv₂ bij • f-equal (Bijection.⟶ bij) (Bijection.inv₂ bij') 
  }

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (succ n)
  succ : {n : Nat} -> Fin n -> Fin (succ n)

Fin-one-mere-prop : MereProp (Fin (succ zero))
Fin-one-mere-prop zero zero = refl
Fin-one-mere-prop _ (succ ())
Fin-one-mere-prop (succ ()) zero

zero-not-succ-Fin : {n : Nat} {a : Fin (succ n)} -> ¬ (Fin.zero ≡ Fin.succ a)
zero-not-succ-Fin {n} {a} p = ap (f-equal family p) tt
  where
  family : Fin (succ (succ n)) -> Set
  family zero = ⊤
  family (succ n) = ⊥

Fin-succ-inj : {n : Nat} {a b : Fin n} -> Fin.succ a ≡ Fin.succ b -> a ≡ b
Fin-succ-inj refl = refl


skip-Fin : {n : Nat} -> Fin (succ (succ n)) -> Fin (succ (succ n)) -> Fin (succ n)
skip-Fin zero zero = zero
skip-Fin zero (succ a) = a
skip-Fin (succ p) zero = zero
skip-Fin {zero} p a = zero
skip-Fin {succ n} (succ p) (succ a) = succ (skip-Fin p a)

skip-Fin-zero-succ : {n : Nat} {x : Fin (succ n)} -> skip-Fin zero (succ x) ≡ x
skip-Fin-zero-succ {zero} {zero} = refl
skip-Fin-zero-succ {zero} {succ ()}
skip-Fin-zero-succ {succ n} {x} = refl

succ-skip-Fin-zero : {n : Nat} {x : Fin (succ (succ n))} -> ¬ (x ≡ zero) -> succ (skip-Fin zero x) ≡ x
succ-skip-Fin-zero {n} {zero} p = absurd (p refl)
succ-skip-Fin-zero {n} {succ x} p = refl

unskip-Fin : {n : Nat} -> Fin (succ (succ n)) -> Fin (succ n) -> Fin (succ (succ n))
unskip-Fin {zero} zero a = succ zero
unskip-Fin {zero} (succ _) a = zero  -- complete the enumeration?
unskip-Fin {succ n} zero a = succ a
unskip-Fin {succ n} (succ p) zero = zero
unskip-Fin {succ n} (succ p) (succ a) = succ (unskip-Fin p a)

skip-unskip-equal : {n : Nat} (p : Fin (succ (succ n))) {x : Fin (succ n)} -> skip-Fin p (unskip-Fin p x) ≡ x
skip-unskip-equal {zero} zero {zero} = refl
skip-unskip-equal {zero} (succ p) {zero} = refl
skip-unskip-equal {zero} p {succ ()}
skip-unskip-equal {succ n} zero {x} = refl
skip-unskip-equal {succ n} (succ p) {zero} = refl
skip-unskip-equal {succ n} (succ p) {succ x} = f-equal succ (skip-unskip-equal p)

unskip-skip-equal : {n : Nat} (p : Fin (succ (succ n))) (x : Fin (succ (succ n))) -> ¬ (p ≡ x) -> unskip-Fin p (skip-Fin p x) ≡ x
unskip-skip-equal {zero} zero zero pt = absurd (pt refl)
unskip-skip-equal {zero} zero (succ zero) pt = refl
unskip-skip-equal {zero} zero (succ (succ ())) pt
unskip-skip-equal {zero} (succ p) zero pt = refl
unskip-skip-equal {zero} (succ zero) (succ zero) pt = absurd (pt refl)
unskip-skip-equal {zero} (succ (succ ())) (succ zero) pt
unskip-skip-equal {zero} (succ p) (succ (succ ())) pt
unskip-skip-equal {succ n} zero zero pt = absurd (pt refl)
unskip-skip-equal {succ n} zero (succ x) pt = refl
unskip-skip-equal {succ n} (succ p) zero pt = refl
unskip-skip-equal {succ n} (succ p) (succ x) pt = f-equal succ (unskip-skip-equal p x (pt ∘ f-equal succ))

unskip-pivot-not-equal : {n : Nat} -> (p : Fin (succ (succ n))) (x : Fin (succ n)) -> ¬ (unskip-Fin p x ≡ p)
unskip-pivot-not-equal {zero} zero x pf = zero-not-succ-Fin (sym-equal pf)
unskip-pivot-not-equal {zero} (succ p) x pf = zero-not-succ-Fin pf
unskip-pivot-not-equal {succ n} zero x pf = zero-not-succ-Fin (sym-equal pf)
unskip-pivot-not-equal {succ n} (succ p) zero pf = zero-not-succ-Fin pf
unskip-pivot-not-equal {succ n} (succ p) (succ x) pf = unskip-pivot-not-equal p x (Fin-succ-inj pf)


swizzle : {m n : Nat} -> Bijection (Fin (succ (succ m))) (Fin (succ (succ n))) -> Bijection (Fin (succ m)) (Fin (succ n))
swizzle bij =
  let pivot = Bijection.⟶ bij zero in
  record {
    ⟶ = skip-Fin pivot ∘ Bijection.⟶ bij ∘ succ ;
    ⟵ = skip-Fin zero ∘ Bijection.⟵ bij ∘ unskip-Fin pivot ;
    inv₁ = \{x} -> let bij-one-not-pivot : ¬ (Bijection.⟶ bij (succ x) ≡ pivot)
                       bij-one-not-pivot = zero-not-succ-Fin ∘ sym-equal ∘ bijection-inj bij
                       x' = Bijection.⟶ bij (succ x)
                   in f-equal (skip-Fin zero ∘ Bijection.⟵ bij) (unskip-skip-equal pivot x' (bij-one-not-pivot ∘ sym-equal)) 
                     • f-equal (skip-Fin zero) (Bijection.inv₁ bij)
                     • skip-Fin-zero-succ ;
    inv₂ = \{x} -> let bij-unskip-pivot-not-zero : ¬ (Bijection.⟵ bij (unskip-Fin pivot x) ≡ zero)
                       bij-unskip-pivot-not-zero p = unskip-pivot-not-equal pivot x (Bijection.inv₂ bij • f-equal (Bijection.⟶ bij) p)
                   in path-ind (\ [] -> x ≡ skip-Fin pivot (Bijection.⟶ bij [])) (sym-equal (succ-skip-Fin-zero bij-unskip-pivot-not-zero))
                     (path-ind (\ [] -> x ≡ skip-Fin pivot []) (Bijection.inv₂ bij) 
                      (sym-equal (skip-unskip-equal pivot)))
  }

Fin-no-bijection-zero : {n : Nat} -> ¬ (Bijection (Fin zero) (Fin (succ n)))
Fin-no-bijection-zero bij with Bijection.⟵ bij zero
...                          | ()

Fin-no-bijection-one : {n : Nat} -> ¬ (Bijection (Fin (succ zero)) (Fin (succ (succ n))))
Fin-no-bijection-one bij = zero-not-succ-Fin (Fin-two-mere-prop zero (succ zero))
  where
  Fin-two-mere-prop = Bijection-mere-prop bij Fin-one-mere-prop
  
  


Fin-downgrade : {m n : Nat} -> Bijection (Fin (succ m)) (Fin (succ n)) -> Bijection (Fin m) (Fin n)
Fin-downgrade {zero} {zero} bij = identity-bijection
Fin-downgrade {zero} {succ n} bij = absurd (Fin-no-bijection-one bij)
Fin-downgrade {succ m} {zero} bij = absurd (Fin-no-bijection-one (sym-bijection bij))
Fin-downgrade {succ m} {succ n} bij = swizzle bij


Fin-no-bijection : {m n : Nat} -> ¬ (m ≡ n) -> ¬ (Bijection (Fin m) (Fin n))
Fin-no-bijection {zero} {zero} p bij = absurd (p refl)
Fin-no-bijection {zero} {succ n} p bij with Bijection.⟵ bij zero
...                                       | ()
Fin-no-bijection {succ m} {zero} p bij with Bijection.⟶ bij zero
...                                       | ()
Fin-no-bijection {succ m} {succ n} p bij = 
  Fin-no-bijection {m} {n} (\p' -> p (f-equal succ p')) (Fin-downgrade bij)




Fin-injection : {m n : Nat} -> Bijection (Fin m) (Fin n) -> m ≡ n
Fin-injection {zero} {zero} = \_ -> refl
Fin-injection {zero} {succ n} = absurd ∘ Fin-no-bijection zero-not-succ
Fin-injection {succ m} {zero} = absurd ∘ Fin-no-bijection (zero-not-succ ∘ sym-equal)
Fin-injection {succ m} {succ n} = f-equal succ ∘ Fin-injection ∘ Fin-downgrade

Fin-injective : {m n : Nat} -> Fin m ≡ Fin n -> m ≡ n
Fin-injective p = Fin-injection (equality-bijection p)
