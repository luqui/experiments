{-# OPTIONS --type-in-type #-}

module hott-model where


open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Data.Unit
open import Data.Empty

Π : (A : Set) (F : A -> Set) -> Set
Π A F = (a : A) -> F a

postulate
  Π-= : {A : Set} {F : A -> Set} {f g : Π A F} -> ((x : A) -> f x ≡ g x) -> f ≡ g


record Σ (A : Set) (F : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : F fst

_×_ : Set -> Set -> Set
A × B = Σ A (\_ -> B)


data _⊔_ (A B : Set) : Set where
  inl : A -> A ⊔ B
  inr : B -> A ⊔ B



record Eqv (A B : Set) : Set where
  field
    f : A -> B
    g : B -> A
    f-g : ∀ x -> f (g x) ≡ x
    g-f : ∀ x -> g (f x) ≡ x
    adj : ∀ x -> cong g (f-g x) ≡ g-f (g x)

_≃_ = Eqv

idf : (A : Set) -> A -> A
idf _ x = x

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
subst-concat {q = refl} = refl

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(g ∘ f) x = g (f x)

subst-cong : {A B : Set} {F : B -> Set} {g : A -> B} {x y : A} {p : x ≡ y} {body : F (g x)} -> subst (F ∘ g) p body ≡ subst F (cong g p) body
subst-cong {p = refl} = refl

cong-sym-commute : {A B : Set} {f : A -> B} {x y : A} {p : x ≡ y} -> cong f (sym p) ≡ sym (cong f p)
cong-sym-commute {p = refl} = refl

-- Can't do this shit in HoTT.  What a load off.
≡-mere-prop : {A : Set} {x y : A} {p q : x ≡ y} -> p ≡ q
≡-mere-prop {p = refl} {q = refl} = refl

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
         ≡⟨ cong (\p -> subst F p _) (Eqv.adj e _) ⟩
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
Eqv.adj (Σ-respects-Eqv e) _ = ≡-mere-prop


cong-dep : {A : Set} {F : A -> Set} (f : (x : A) -> F x) {a b : A} (p : a ≡ b) -> subst F p (f a) ≡ f b
cong-dep _ refl = refl

Π-respects-Eqv : {A B : Set} (e : A ≃ B) {F : A -> Set} -> Π A F ≃ Π B (F ∘ Eqv.g e)
Eqv.f (Π-respects-Eqv e {F = F}) t b = t (Eqv.g e b)
Eqv.g (Π-respects-Eqv e {F = F}) t a = subst F (Eqv.g-f e a) (t (Eqv.f e a))
Eqv.f-g (Π-respects-Eqv e {F = F}) t = Π-= (\b -> 
   let pfx = subst F (Eqv.g-f e (Eqv.g e b)) in
   begin
     subst F (Eqv.g-f e (Eqv.g e b)) (t (Eqv.f e (Eqv.g e b)))
       ≡⟨ cong pfx (sym (cong-dep t (sym (Eqv.f-g e b)))) ⟩
     subst F (Eqv.g-f e (Eqv.g e b)) (subst (F ∘ Eqv.g e) (sym (Eqv.f-g e b)) (t b))
       ≡⟨ cong pfx (subst-cong {p = sym (Eqv.f-g e b)}) ⟩
     subst F (Eqv.g-f e (Eqv.g e b)) (subst F (cong (Eqv.g e) (sym (Eqv.f-g e b))) (t b))
       ≡⟨ cong (\ ◼ -> pfx (subst F ◼ (t b))) (cong-sym-commute {p = Eqv.f-g e b})  ⟩
     subst F (Eqv.g-f e (Eqv.g e b)) (subst F (sym (cong (Eqv.g e) (Eqv.f-g e b))) (t b))
       ≡⟨ cong (\ ◼ -> pfx (subst F (sym ◼) (t b))) (Eqv.adj e _) ⟩
     subst F (Eqv.g-f e (Eqv.g e b)) (subst F (sym (Eqv.g-f e (Eqv.g e b))) (t b))
       ≡⟨ subst-concat {p = Eqv.g-f e (Eqv.g e b)} {q = sym (Eqv.g-f e (Eqv.g e b))} ⟩
     subst F (sym (Eqv.g-f e (Eqv.g e b)) ∙ Eqv.g-f e (Eqv.g e b)) (t b)
       ≡⟨ cong (\ ■ -> subst F ■ (t b)) (sym-id-refl (Eqv.g-f e (Eqv.g e b))) ⟩
     subst F refl (t b)
       ≡⟨ refl ⟩
     t b
   ∎)
Eqv.g-f (Π-respects-Eqv e {F = F}) t = Π-= (\a -> 
   begin
     subst F (Eqv.g-f e a) (t (Eqv.g e (Eqv.f e a)))
        ≡⟨ cong (subst F (Eqv.g-f e a)) (sym (cong-dep t (sym (Eqv.g-f e a)))) ⟩
     subst F (Eqv.g-f e a) (subst F (sym (Eqv.g-f e a)) (t a))
        ≡⟨ subst-concat {p = Eqv.g-f e a} {q = sym (Eqv.g-f e a)} ⟩
     subst F (sym (Eqv.g-f e a) ∙ Eqv.g-f e a) (t a) 
        ≡⟨ cong (\ ◼ -> subst F ◼ (t a)) (sym-id-refl (Eqv.g-f e a)) ⟩
     subst F refl (t a)
        ≡⟨ refl ⟩
     t a
   ∎)
Eqv.adj (Π-respects-Eqv e) _ = ≡-mere-prop


record Type : Set where
  constructor _/[_]
  field
    T : Set
    eq : T -> T -> Set

-- lolz so lazy.  obv this should be part of Type.
-- Is it enough to require eq be an equivalence relation?  So far we have
-- only needed reflexivity, and later we will need elimination which is
-- much stronger than equivalence relation (unless all functions being
-- eq-homomorphisms takes care of that for us, which would be sweet).
postulate
  lazyrefl : (A : Type) {x : Type.T A} -> Type.eq A x x

record Hom (A B : Type) : Set where
  field
    f : Type.T A -> Type.T B
    hom : {x y : Type.T A} -> Type.eq A x y -> Type.eq B (f x) (f y)

_∘H_ : {A B C : Type} -> Hom B C -> Hom A B -> Hom A C
Hom.f (h ∘H g) = Hom.f h ∘ Hom.f g
Hom.hom (h ∘H g) = Hom.hom h ∘ Hom.hom g

IdHom : (A : Type) -> Hom A A
Hom.f (IdHom A) x = x
Hom.hom (IdHom A) x = x

_~>_ : Type -> Type -> Type
A ~> B = Hom A B /[ (\f g -> (x : Type.T A) -> Type.eq B (Hom.f f x) (Hom.f g x)) ]


TypeT = Type /[ (\t u -> Σ (Hom t u × Hom u t) (\{ (f , g) ->
           Type.eq (u ~> u) (f ∘H g) (IdHom u) × Type.eq (t ~> t) (g ∘H f) (IdHom t) })) ]

SigmaT : (A : Type) -> Hom A TypeT -> Type
SigmaT A F = Σ (Type.T A) (Type.T ∘ Hom.f F) /[ 
    (\{ (x , y) (x' , y') -> Σ (Type.eq A x x') (\p -> 
       let e = Hom.hom F p
           Fx→Fx' = Hom.f (Σ.fst (Σ.fst e))
       in Type.eq (Hom.f F x') (Fx→Fx' y) y' ) }) ]

ProdT : Type -> Type -> Type
ProdT A B = SigmaT A record { f = \_ -> B ; hom = \_ -> (IdHom B , IdHom B) , ((\_ -> lazyrefl B) , (\_ -> lazyrefl B)) }

PiT : (A : Type) -> Hom A TypeT -> Type
PiT A F = Π (Type.T A) (Type.T ∘ Hom.f F) /[
    (\f g -> (x : Type.T A) -> Type.eq (Hom.f F x) (f x) (g x)) ]

CoprodT : Type -> Type -> Type
CoprodT A B = (Type.T A ⊔ Type.T B) /[ (
    \{ (inl x) (inl y) -> Type.eq A x y ;
       (inr x) (inr y) -> Type.eq B x y ;
       _ _ -> ⊥ } ) ]

UnitT : Type
UnitT = ⊤ /[ (\{ tt tt -> ⊤ }) ]

EmptyT : Type
EmptyT = ⊥ /[ (\()) ]

-- Seems like this is the moment of truth for univalence.  For true HoTT Type.eq should be a Type
-- (which is what Hom is expecting here in any case), not a Set.  We might have to delve into coinductive
-- records and I fear things will get quite complicated...
IdT : (A : Type) -> Hom (ProdT A A) TypeT
IdT A = record {
    f = \{ (x , y) -> {!Type.eq A x y!} } ;
    hom = {!!} }
