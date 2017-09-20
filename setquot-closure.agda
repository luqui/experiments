{-# OPTIONS --without-K --rewriting #-}

module setquot-closure where

-- I noticed that SetQuot R didn't require R to be an equivalence relation to be
-- well-defined, and wondered what it would mean if it weren't one.  This short
-- development answers that question, that it's equivalent to SetQuot (Closure R),
-- where Closure R is the smallest equivalence relation containing R.

open import HoTT

record is-eqv-rel {ℓ i} {A : Set ℓ} (R : Rel A i) : Set (lmax ℓ i) where
  field
    refl : ∀ {x} -> R x x
    sym : ∀ {x y} -> R x y -> R y x
    trans : ∀ {x y z} -> R x y -> R y z -> R x z

-- Definition of containment for relations.
_⊂_ : ∀ {ℓ i j} {A : Set ℓ} -> Rel A i -> Rel A j -> Set (lmax ℓ (lmax i j))
_⊂_ R R' = ∀ {x y} -> R x y -> R' x y


-- A closure of R is "a smallest" equivalence relation containing R. 
record is-closure {ℓ i j} {A : Set ℓ} (R : Rel A i) (R* : Rel A j) 
          : Set (lmax ℓ (lmax (lsucc i) j)) where
  field
    eqv-rel : is-eqv-rel R*
    contains-R : R ⊂ R*
    smallest : (R' : Rel A i) -> is-eqv-rel R' -> R ⊂ R' -> R* ⊂ R'

-- Closure j R is one way of constructing a closure of R. The index j tells us what universe 
-- to quantify over: that is, it's the least of all such relations in universe j.  Notice that 
-- Closure is not itself in universe j.
Closure : ∀ {ℓ i} {A : Set ℓ} -> ∀ j -> Rel A i -> Rel A (lmax ℓ (lmax i (lsucc j)))
Closure {ℓ} {i} {A} j R = \x y -> (R' : Rel A j) -> is-eqv-rel R' -> R ⊂ R' -> R' x y

module Closure {ℓ i} {A : Set ℓ} {R : Rel A i} where
  -- Closure is in fact an equivalence relation,...
  Closure-is-eqv-rel : is-eqv-rel (Closure i R)
  Closure-is-eqv-rel = record
    { refl = \R' eqv subrel -> is-eqv-rel.refl eqv
    ; sym = \rxy R' eqv subrel -> is-eqv-rel.sym eqv (rxy R' eqv subrel)
    ; trans = \rxy ryz R' eqv subrel -> is-eqv-rel.trans eqv (rxy R' eqv subrel) (ryz R' eqv subrel)
    }

  Closure-is-closure : is-closure R (Closure i R)
  Closure-is-closure = record
    { eqv-rel = Closure-is-eqv-rel
    ; contains-R = \rxy R' eqv subrel -> subrel rxy
    ; smallest   = \R' eqv subrel qxy -> qxy R' eqv subrel
    }

-- Just some notation, q[ x ]/ R, the equivalence class of x by R.
infix 90 q[_]/_
q[_]/_ : ∀ {ℓ i} {A : Set ℓ} -> A -> (R : Rel A i) -> SetQuot R
q[ x ]/ R = q[ x ]


module _ {ℓ i j} {A : Set ℓ} 
         {R : Rel A (lmax ℓ i)}  -- (This universe level is a little weird, needed b/c the
                                 --  quantifiction in is-closure.smallest. Probably could be
                                 --  cleaned up.)
         {R* : Rel A j} 
         (R*-is-closure : is-closure R R*) where
  private
    -- This tiny definition is the key to the whole development (look at where
    -- it is used below in `from`).  Closure R can be thought of as R with extra edges added to make 
    -- it an equivalence relation.  When we pass q=-EqvRel to a Closure R, we "interpret" those edges
    -- as equalities in SetQuot R, which might not immediately follow from quot-rel (e.g.
    -- it might take a few quot-rel's and transitivity). The fact that those edges can always be
    -- interepreted in SetQuot R comes from the fact that quot-rel's codomain is an equivalence 
    -- relation.
    q= : (x y : A) -> Set _
    q= x y = q[ x ]/ R == q[ y ]/ R

    q=-is-eqv-rel : is-eqv-rel q=
    q=-is-eqv-rel = record
      { refl = idp
      ; sym = !
      ; trans = _∙_
      }

    is-set-all-PathOver-paths : ∀ {i j} {A : Set i} {B : A -> Set j} 
      -> ((x : A) -> is-set (B x))
      -> (f g : Π A B) 
      -> {x y : A} (s : x == y)
      -> {p : f x == g x} {q : f y == g y}
      -> PathOver (\x -> f x == g x) s p q
    is-set-all-PathOver-paths isset f g {x = x} idp {p} {q} = fst (isset x (f x) (g x) p q) 


  -- And the punchline.
  SetQuot-preserves-closure : SetQuot R ≃ SetQuot R*
  SetQuot-preserves-closure = equiv to from to-from from-to
    where
    to : SetQuot R -> SetQuot R*
    to = SetQuot-rec {B = SetQuot R*} SetQuot-level (\x -> q[ x ]) 
            (quot-rel ∘ is-closure.contains-R R*-is-closure)
  
    from : SetQuot R* -> SetQuot R
    from = SetQuot-rec {B = SetQuot R} SetQuot-level (\x -> q[ x ])
             (is-closure.smallest R*-is-closure q= q=-is-eqv-rel quot-rel)

    to-from : ∀ x -> to (from x) == x
    to-from = SetQuot-elim {P = \q -> to (from q) == q} 
                 (\x -> raise-level _ (SetQuot-level (to (from x)) x)) 
                 (\a -> idp)
                 (\r -> is-set-all-PathOver-paths (\_ -> SetQuot-level) 
                                                  (\x -> to (from x)) (\x -> x)
                                                  (quot-rel r))

    from-to : ∀ x -> from (to x) == x
    from-to = SetQuot-elim {P = \q -> from (to q) == q}
                 (\x -> raise-level _ (SetQuot-level (from (to x)) x))
                 (\a -> idp)
                 (\r -> is-set-all-PathOver-paths (\_ -> SetQuot-level) 
                                                  (\x -> from (to x)) (\x -> x)
                                                  (quot-rel r))
