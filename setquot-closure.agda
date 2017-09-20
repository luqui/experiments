{-# OPTIONS --without-K --rewriting #-}

module setquot-closure where

open import HoTT

record EqvRel {ℓ i} {A : Set ℓ} (R : Rel A i) : Set (lmax ℓ i) where
  field
    refl : ∀ {x} -> R x x
    sym : ∀ {x y} -> R x y -> R y x
    trans : ∀ {x y z} -> R x y -> R y z -> R x z


_⊂_ : ∀ {ℓ i j} {A : Set ℓ} -> Rel A i -> Rel A j -> Set (lmax ℓ (lmax i j))
_⊂_ R R' = ∀ {x y} -> R x y -> R' x y

=-EqvRel : ∀ {ℓ} {A : Set ℓ} -> EqvRel (_==_ {A = A})
=-EqvRel = record
  { refl = idp
  ; sym = !
  ; trans = _∙_
  }

q=-EqvRel : ∀ {ℓ i} {A : Set ℓ} {R : Rel A i} -> EqvRel (\x y ->  q[_] {R = R} x == q[ y ])
q=-EqvRel = record
  { refl = idp
  ; sym = !
  ; trans = _∙_
  }

Free : ∀ {ℓ i} {A : Set ℓ} -> ∀ j -> Rel A i -> Rel A (lmax ℓ (lmax i (lsucc j)))
Free {ℓ} {i} {A} j R = \x y -> (R' : Rel A j) -> EqvRel R' -> R ⊂ R' -> R' x y

Free-EqvRel : ∀ {ℓ i j} {A : Set ℓ} {R : Rel A i} -> EqvRel (Free j R)
Free-EqvRel = record
  { refl = \R' eqv subrel -> EqvRel.refl eqv
  ; sym = \rxy R' eqv subrel -> EqvRel.sym eqv (rxy R' eqv subrel)
  ; trans = \rxy ryz R' eqv subrel -> EqvRel.trans eqv (rxy R' eqv subrel) (ryz R' eqv subrel)
  }

Free-subrel : ∀ {ℓ i j} {A : Set ℓ} {R : Rel A i} -> R ⊂ Free j R
Free-subrel rxy R' eqv subrel = subrel rxy

Free-least : ∀ {ℓ i j} {A : Set ℓ} {R : Rel A i} {R' : Rel A j} 
          -> R ⊂ R' -> EqvRel R' -> Free j R ⊂ R'
Free-least subrel eqv freerxy = freerxy _ eqv subrel

is-set-all-PathOver-paths : ∀ {i j} {A : Set i} {B : A -> Set j} 
      -> ((x : A) -> is-set (B x))
      -> (f g : Π A B) 
      -> {x y : A} (s : x == y)
      -> {p : f x == g x} {q : f y == g y}
      -> PathOver (\x -> f x == g x) s p q
is-set-all-PathOver-paths isset f g {x = x} idp {p} {q} = fst (isset x (f x) (g x) p q) 

SetQuot-preserves-closure : ∀ {ℓ} {i} {A : Set ℓ} {R : Rel A i} 
                         -> SetQuot R ≃ SetQuot (Free (lmax ℓ i) R)
SetQuot-preserves-closure {ℓ} {i} {A} {R} = equiv to from to-from from-to
  where
  to : SetQuot R -> SetQuot (Free (lmax ℓ i) R)
  to = SetQuot-rec {B = SetQuot (Free (lmax ℓ i) R)} SetQuot-level (\x -> q[ x ]) 
          (\rxy -> quot-rel (Free-subrel rxy))
  
  from : SetQuot (Free (lmax ℓ i) R) -> SetQuot R
  from = SetQuot-rec {B = SetQuot R} SetQuot-level (\x -> q[ x ])
           (\freerxy -> freerxy _ q=-EqvRel quot-rel )

  to-from : ∀ x -> to (from x) == x
  to-from = SetQuot-elim {P = \q -> to (from q) == q} 
               (\x -> raise-level _ (SetQuot-level (to (from x)) x)) 
               (\a -> idp)
               (\r -> is-set-all-PathOver-paths (\_ -> SetQuot-level) (\x -> to (from x)) (\x -> x) (quot-rel r))

  from-to : ∀ x -> from (to x) == x
  from-to = SetQuot-elim {P = \q -> from (to q) == q}
               (\x -> raise-level _ (SetQuot-level (from (to x)) x))
               (\a -> idp)
               (\r -> is-set-all-PathOver-paths (\_ -> SetQuot-level) (\x -> from (to x)) (\x -> x) (quot-rel r))
