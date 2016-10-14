{-# OPTIONS --type-in-type #-}

module hott-model where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

record Σ (A : Set) (F : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : F fst

Π : (A : Set) (F : A -> Set) -> Set
Π A F = (a : A) -> F a


record Eqv (A B : Set) : Set where
  field
    f : A -> B
    g : B -> A
    f-g : ∀ x -> f (g x) ≡ x
    g-f : ∀ x -> g (f x) ≡ x

_≃_ = Eqv

EqOver : {A : Set} (F : A -> Set) {x y : A} (p : x ≡ y) (u : F x) (v : F y) -> Set
EqOver F refl u v = u ≡ v

≡-elim : {A : Set} {x : A} (F : (q : A) -> x ≡ q -> Set) {y : A} -> F x refl -> (p : x ≡ y) -> F y p
≡-elim _ body refl = body

Σ-≡ : {A : Set} {F : A -> Set} {u v : Σ A F} -> (p : Σ.fst u ≡ Σ.fst v) -> EqOver F p (Σ.snd u) (Σ.snd v) -> u ≡ v
Σ-≡ refl refl = refl

_∙_ : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
refl ∙ p = p

mkEqOver : {A : Set} {F : A -> Set} {x y : A} {u : F x} {v : F y} {p : x ≡ y} -> subst F p u ≡ v -> EqOver F p u v
mkEqOver {p = refl} q = q

subst-concat : {A : Set} {F : A -> Set} {x y z : A} {p : y ≡ z} {q : x ≡ y} {body : F x} -> subst F p (subst F q body) ≡ subst F (q ∙ p) body
subst-concat {p = refl} {q = refl} = refl

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(g ∘ f) x = g (f x)

subst-cong : {A B : Set} {F : B -> Set} {g : A -> B} {x y : A} {p : x ≡ y} {body : F (g x)} -> subst (F ∘ g) p body ≡ subst F (cong g p) body
subst-cong {p = refl} = refl

-- Can't do this shit in HoTT.  What a load off.
≡-mere-prop : {A : Set} {x y : A} {p q : x ≡ y} -> p ≡ q
≡-mere-prop {p = refl} {q = refl} = refl

eqv-cong-g' :  {A B : Set} {e : A ≃ B} {b : B} -> cong (Eqv.g e) (Eqv.f-g e b) ≡ Eqv.g-f e (Eqv.g e b)
eqv-cong-g' = ≡-mere-prop

sym-id-refl : {A : Set} {x y : A} (p : x ≡ y) -> (sym p ∙ p) ≡ refl
sym-id-refl refl = refl

Σ-respects-Eqv : {A B : Set} (e : A ≃ B) {F : A -> Set} -> Σ A F ≃ Σ B (F ∘ Eqv.g e)
Eqv.f (Σ-respects-Eqv e {F = F}) (a , x) = Eqv.f e a , subst F (sym (Eqv.g-f e _)) x
Eqv.g (Σ-respects-Eqv e {F = F}) (b , x) = Eqv.g e b , x
Eqv.f-g (Σ-respects-Eqv e {F = F}) (b , x) = Σ-≡ (Eqv.f-g e b) (mkEqOver (
   begin
     subst (F ∘ Eqv.g e) (Eqv.f-g e b) (subst F (sym (Eqv.g-f e (Eqv.g e b))) x) 
         ≡⟨ subst-cong {p = Eqv.f-g e b} ⟩
     subst F (cong (Eqv.g e) (Eqv.f-g e b)) (subst F (sym (Eqv.g-f e (Eqv.g e b))) x)
         ≡⟨ cong (\p -> subst F p _) (eqv-cong-g' {e = e}) ⟩
     subst F (Eqv.g-f e (Eqv.g e b)) (subst F (sym (Eqv.g-f e (Eqv.g e b))) x)
         ≡⟨ subst-concat {p = Eqv.g-f e (Eqv.g e b)} {q = sym (Eqv.g-f e (Eqv.g e b))}  ⟩
     subst F (sym (Eqv.g-f e (Eqv.g e b)) ∙ Eqv.g-f e (Eqv.g e b)) x
         ≡⟨ cong (\p -> subst F p x) (sym-id-refl (Eqv.g-f e (Eqv.g e b))) ⟩
     subst F refl x
         ≡⟨ refl ⟩
     x
   ∎))
Eqv.g-f (Σ-respects-Eqv e {F = F}) (a , x) = Σ-≡ (Eqv.g-f e a) (mkEqOver (
   begin 
     subst F (Eqv.g-f e a) (subst F (sym (Eqv.g-f e a)) x)    ≡⟨ subst-concat {p = Eqv.g-f e a} {q = sym (Eqv.g-f e a)} ⟩
     subst F (sym (Eqv.g-f e a) ∙ Eqv.g-f e a) x              ≡⟨ cong (\p -> subst F p x) (sym-id-refl (Eqv.g-f e a)) ⟩
     subst F refl x                                           ≡⟨ refl ⟩
     x
   ∎))


Π-respects-Eqv : {A B : Set} (e : A ≃ B) {F : A -> Set} -> Π A F ≃ Π B (F ∘ Eqv.g e)
Eqv.f (Π-respects-Eqv e {F = F}) f b = {!!}
Eqv.g (Π-respects-Eqv e {F = F}) f a = {!!}
Eqv.f-g (Π-respects-Eqv e {F = F}) f = {!!}
Eqv.g-f (Π-respects-Eqv e {F = F}) f = {!!}
