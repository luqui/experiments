module hott-play where

open import Level
  using (Level ; _⊔_)
  renaming (suc to lsuc)

infixl 9 _∘_
_∘_ : {l : Level} {A B C : Set l} -> (B -> C) -> (A -> B) -> (A -> C)
(g ∘ f) x = g (f x)

id : {l : Level} {A : Set l} -> (A -> A)
id x = x


data ⊥ {l} : Set l where

data ⊤ {l} : Set l where
  tt : ⊤

¬_ : {l m : Level} (A : Set l) -> Set (l ⊔ m)
¬_ {l} {m} A = A -> ⊥ {m}


data _≡_ {l} {A : Set l} (x : A) : A -> Set l where
  refl : x ≡ x

id-ind : {l : Level} {A : Set l} 
      -> (C : (x y : A) -> x ≡ y -> Set l)
      -> (c : (x : A) -> C x x refl)
      -> {x y : A} (p : x ≡ y) -> C x y p
id-ind C c {x} {.x} refl = c x

id-based-ind : {l : Level} {A : Set l} {a : A}
            -> (C : (x : A) -> a ≡ x -> Set l)
            -> (c : C a refl)
            -> {x : A} (p : a ≡ x) -> C x p
id-based-ind C c {x} refl = c

f-equal : {l m : Level} {A : Set l} {B : Set m} (f : A -> B) {x y : A}
        -> x ≡ y -> f x ≡ f y
f-equal _ refl = refl

id-sym : {l : Level} {A : Set l} {x y : A} -> x ≡ y -> y ≡ x
id-sym refl = refl

infixl 9 _•_
_•_ : {l : Level} {A : Set l} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
refl • refl = refl

•-left-cancel : {l : Level} {A : Set l} 
              -> {x y z : A}
              -> {p : x ≡ y} {q r : y ≡ z}
              -> (p • q) ≡ (p • r) -> q ≡ r
•-left-cancel {p = refl} {q = refl} {r = refl} = id


postulate
  ex : {l m : Level} {A : Set l} {P : A -> Set m} {f g : (x : A) -> P x}
    -> ((x : A) -> f x ≡ g x) -> f ≡ g

record Σ {l m} (A : Set l) (P : A -> Set m) : Set (l ⊔ m) where
  constructor _∥_
  field
    proj₁ : A
    proj₂ : P proj₁



record isEquiv {l} (A B : Set l) (f : A -> B) : Set (lsuc l) where
  constructor isequiv
  field
    inv-post : Σ (B -> A) (\g -> (g ∘ f) ≡ id)
    inv-pre  : Σ (B -> A) (\g -> (f ∘ g) ≡ id)

_≅_ : {l : Level} -> Set l -> Set l -> Set (lsuc l)
A ≅ B = Σ (A -> B) (\f -> isEquiv A B f)

isEquiv-set : {l : Level} {A B : Set l} {f : A -> B} (e e' : isEquiv A B f) -> e ≡ e'
isEquiv-set {l} {A} {B} {f} (isequiv pre post) (isequiv pre' post') = {!!}

ap-eqv : {l : Level} {A B : Set l} -> A ≅ B -> A -> B
ap-eqv (f ∥ _) = f

id-eqv : {l : Level} {A : Set l} -> A ≅ A
id-eqv {A} = id ∥ isequiv (id ∥ refl) (id ∥ refl)

transport : {l m : Level} {A : Set l} (P : A -> Set m)
          -> {x y : A} -> x ≡ y -> P x ≅ P y
transport _ refl = id-eqv

ap : {l m : Level} {A : Set l} (P : A -> Set m)
         -> {x y : A} -> x ≡ y -> (P x -> P y)
ap P p = Σ.proj₁ (transport P p)

idtoeqv : {l : Level} {A B : Set l} -> (A ≡ B) -> (A ≅ B)
idtoeqv = transport id

lemma-isEquiv-unique-inverse : {l : Level} {A B : Set l} (f : A -> B) (eqv : isEquiv _ _ f)
                            -> (Σ.proj₁ (isEquiv.inv-pre eqv) ≡ Σ.proj₁ (isEquiv.inv-post eqv))
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

eqv-sym : {l : Level} -> {A B : Set l} -> A ≅ B -> B ≅ A
eqv-sym (f ∥ isequiv (g ∥ p) (g' ∥ p')) = 
  g ∥ isequiv (f ∥ ap (\G -> (\x -> f (G x)) ≡ id) g-g'-id p') (f ∥ p)
  where
  g-g'-id : g' ≡ g
  g-g'-id = lemma-isEquiv-unique-inverse f (isequiv (g ∥ p) (g' ∥ p'))



postulate
  ua-axiom : {l : Level} {A B : Set l} -> isEquiv (A ≡ B) (A ≅ B) idtoeqv

ua : {l : Level} {A B : Set l} -> A ≅ B -> A ≡ B 
ua {_} {A} {B} eqv = Σ.proj₁ (isEquiv.inv-pre ua-axiom) eqv

ua' : {l : Level} {A B : Set l} -> A ≅ B -> A ≡ B
ua' {_} {A} {B} eqv = Σ.proj₁ (isEquiv.inv-post ua-axiom) eqv

ua-ua'-id : {l : Level} {A B : Set l} -> ua {l} {A} {B} ≡ ua' {l} {A} {B}
ua-ua'-id = lemma-isEquiv-unique-inverse _ ua-axiom

lem-ua-compute : {l : Level} {A B : Set l} (f : A ≅ B) -> idtoeqv (ua f) ≡ f
lem-ua-compute {l} {A} {B} f = f-equal (\k -> k f) inv-pre-id
  where
  inv-pre-id = Σ.proj₂ (isEquiv.inv-pre (ua-axiom {l} {A} {B})) 

lem-ua-unique : {l : Level} {A B : Set l} (p : A ≡ B) -> p ≡ ua (idtoeqv p)
lem-ua-unique {l} {A} {B} p = ap (\u -> p ≡ u (idtoeqv p)) (id-sym ua-ua'-id) 
                              (f-equal (\k -> k p) inv-post-id)
  where
  inv-post-id = id-sym (Σ.proj₂ (isEquiv.inv-post (ua-axiom {l} {A} {B})))


module Bool where
  data Bool : Set where
    true : Bool
    false : Bool

  true-not-false : ¬ (true ≡ false)
  true-not-false p = ap comp p tt
    where
    comp : Bool -> Set
    comp true = ⊤
    comp false = ⊥

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

  negB-transport : ap (\bool -> bool) negB-id true ≡ false
  negB-transport = f-equal (\k -> Σ.proj₁ k true) (lem-ua-compute negB-eqv)

  idB-transport : ap (\bool -> bool) refl true ≡ true
  idB-transport = refl

  nontrivial-Bool-path : ¬ (negB-id ≡ refl)
  nontrivial-Bool-path p = true-not-false true-equals-false
    where
    negB-transport-sub = f-equal (\p' -> ap (\bool -> bool) p' true ≡ false) p
    true-equals-false = ap id negB-transport-sub negB-transport


  Bool-ind : (P : Bool -> Set) -> P true -> P false -> (x : Bool) -> P x
  Bool-ind _ t _ true = t
  Bool-ind _ _ f false = f


module List (A : Set) where
  data List : Set where
    [] : List
    _∷_ : A -> List -> List

  Unfold : Set₁
  Unfold = (B : Set) -> (A -> B -> B) -> B -> B

  List-to-Unfold : List -> Unfold
  List-to-Unfold [] _ _ nil = nil
  List-to-Unfold (x ∷ xs) B cons nil = cons x (List-to-Unfold xs B cons nil)

  Unfold-to-List : Unfold -> List
  Unfold-to-List u = u List _∷_ []

  List-to-Unfold-id : (xs : List) -> List-to-Unfold xs List _∷_ [] ≡ xs
  List-to-Unfold-id [] = refl
  List-to-Unfold-id (x ∷ xs) = f-equal (_∷_ x) (List-to-Unfold-id xs)

  iso₁ : (xs : List) -> Unfold-to-List (List-to-Unfold xs) ≡ xs
  iso₁ xs = List-to-Unfold-id xs

  u-must-be-empty : (u : Unfold) -> u List _∷_ [] ≡ [] 
                  -> (B : Set) (f : A -> B -> B) (z : B) -> u B f z ≡ z
  u-must-be-empty u p B f z = {!!}

  Unfold-to-List-id : (u : Unfold) (B : Set) (f : A -> B -> B) (z : B) 
                   -> List-to-Unfold (Unfold-to-List u) B f z ≡ u B f z
  Unfold-to-List-id u B f z with u List _∷_ []
  ...                          | [] = {!!}
  ...                          | (x ∷ xs) = {!!}

  iso₂ : (u : Unfold) -> List-to-Unfold (Unfold-to-List u) ≡ u
  iso₂ u = ex (\x -> ex (\f -> {!!}))
