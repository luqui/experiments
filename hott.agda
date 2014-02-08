module hott where

open import Level

data ⊥ {l} : Set l where

_∘_ : {l : Level} {A B C : Set l} -> (B -> C) -> (A -> B) -> (A -> C)
(g ∘ f) x = g (f x)

id : {l : Level} {A : Set l} -> (A -> A)
id x = x

¬_ : {l : Level} (A : Set l) -> Set l
¬_ {l} A = A -> ⊥ {l}


data _≡_ {l} {A : Set l} (x : A) : A -> Set l where
  refl : x ≡ x

ap : {l m : Level} {A : Set l} (P : A -> Set m)
         -> {x y : A} -> x ≡ y -> (P x -> P y)
ap _ refl = id

postulate
  ex : {l m : Level} {A : Set l} {P : A -> Set m} {f g : (x : A) -> P x}
    -> ((x : A) -> f x ≡ g x) -> f ≡ g

data Σ {l m} {A : Set l} (P : A -> Set m) : Set (l ⊔ m) where
  _∥_ : (x : A) -> P x -> Σ P

proj₁ : {l m : Level} {A : Set l} {P : A -> Set m} -> Σ P -> A
proj₁ (x ∥ _) = x



record isEquiv {l} (A B : Set l) (f : A -> B) : Set (suc l) where
  constructor isequiv
  field
    inv-post : Σ (\g -> (g ∘ f) ≡ id)
    inv-pre  : Σ (\g -> (f ∘ g) ≡ id)

_≅_ : {l : Level} -> Set l -> Set l -> Set (suc l)
A ≅ B = Σ (\f -> isEquiv A B f)

ap-eqv : {l : Level} {A B : Set l} -> A ≅ B -> A -> B
ap-eqv (f ∥ _) = f

id-eqv : {l : Level} {A : Set l} -> A ≅ A
id-eqv {A} = id ∥ isequiv (id ∥ refl) (id ∥ refl)

transport : {l m : Level} {A : Set l} (P : A -> Set m)
          -> {x y : A} -> x ≡ y -> P x ≅ P y
transport _ refl = id-eqv

idtoeqv : {l : Level} {A B : Set l} -> (A ≡ B) -> (A ≅ B)
idtoeqv = transport id

lemma-isEquiv-unique-inverse : {l : Level} {A B : Set l} (f : A -> B) (eqv : isEquiv _ _ f)
                            -> (proj₁ (isEquiv.inv-pre eqv) ≡ proj₁ (isEquiv.inv-post eqv))
lemma-isEquiv-unique-inverse f (isequiv (g ∥ invg) (g' ∥ invg')) = α4
  where
  α1 : ((g ∘ f) ∘ g') ≡ (g ∘ (f ∘ g'))
  α1 = refl
  α2 : (id ∘ g') ≡ (g ∘ (f ∘ g'))
  α2 = ap (\k -> (k ∘ g') ≡ (g ∘ (f ∘ g'))) invg α1
  α3 : (id ∘ g') ≡ (g ∘ id)
  α3 = ap (\k -> (id ∘ g') ≡ (g ∘ k)) invg' α2
  α4 : g' ≡ g
  α4 = α3
  


postulate
  ua-axiom : {l : Level} {A B : Set l} -> isEquiv _ _ (idtoeqv {l} {A} {B})

ua : {l : Level} {A B : Set l} -> A ≅ B -> A ≡ B 
ua {_} {A} {B} eqv with ua-axiom {_} {A} {B}
...                   | isequiv (post ∥ _) _ = post eqv


lem-ua-compute : {l : Level} {A B : Set l} (f : A ≅ B) -> idtoeqv (ua f) ≡ f
lem-ua-compute f = {!!}

lem-ua-unique : {l : Level} {A B : Set l} (p : A ≡ B) -> p ≡ ua (idtoeqv p)
lem-ua-unique p = {!!}

data Bool : Set where
  true : Bool
  false : Bool

negB : Bool -> Bool
negB true = false
negB false = true

lemma-negB-self-inverse : (x : Bool) -> negB (negB x) ≡ x
lemma-negB-self-inverse true = refl
lemma-negB-self-inverse false = refl

negB-eqv : Bool ≅ Bool
negB-eqv = negB ∥ isequiv (negB ∥ ex lemma-negB-self-inverse) 
                           (negB ∥ ex lemma-negB-self-inverse)

negB-id : Bool ≡ Bool
negB-id = ua negB-eqv

