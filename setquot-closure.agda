{-# OPTIONS --without-K --rewriting #-}

module setquot-closure where

-- I noticed that SetQuot R didn't require R to be an equivalence relation to be
-- well-defined, and wondered what it would mean if it weren't one.  This short
-- development answers that question, that it's equivalent to SetQuot (Free R),
-- where Free R is the smallest equivalence relation containing R.

open import HoTT

record EqvRel {ℓ i} {A : Set ℓ} (R : Rel A i) : Set (lmax ℓ i) where
  field
    refl : ∀ {x} -> R x x
    sym : ∀ {x y} -> R x y -> R y x
    trans : ∀ {x y z} -> R x y -> R y z -> R x z

-- Definition of containment for relations.
_⊂_ : ∀ {ℓ i j} {A : Set ℓ} -> Rel A i -> Rel A j -> Set (lmax ℓ (lmax i j))
_⊂_ R R' = ∀ {x y} -> R x y -> R' x y

-- Free j R is the least equivalence relation containing R.  The index j tells us
-- what universe to quantify over: that is, it's the least of all such relations
-- in universe j.  Notice that Free is not itself be in universe j (I wonder if
-- it's possible, though).
Free : ∀ {ℓ i} {A : Set ℓ} -> ∀ j -> Rel A i -> Rel A (lmax ℓ (lmax i (lsucc j)))
Free {ℓ} {i} {A} j R = \x y -> (R' : Rel A j) -> EqvRel R' -> R ⊂ R' -> R' x y


module Free {ℓ i j} {A : Set ℓ} {R : Rel A i} where
  -- Free is in fact an equivalence relation,...
  Free-EqvRel : EqvRel (Free j R)
  Free-EqvRel = record
    { refl = \R' eqv subrel -> EqvRel.refl eqv
    ; sym = \rxy R' eqv subrel -> EqvRel.sym eqv (rxy R' eqv subrel)
    ; trans = \rxy ryz R' eqv subrel -> EqvRel.trans eqv (rxy R' eqv subrel) (ryz R' eqv subrel)
    }

  -- Containing R,...
  Free-subrel : R ⊂ Free j R
  Free-subrel rxy R' eqv subrel = subrel rxy

  -- And the least one.
  Free-least : {R' : Rel A j} -> R ⊂ R' -> EqvRel R' -> Free j R ⊂ R'
  Free-least subrel eqv freerxy = freerxy _ eqv subrel

module _ where
  private
    -- Just some notation, q[ x ]/ R, the equivalence class of x by R.
    infix 90 q[_]/_
    q[_]/_ : ∀ {ℓ i} {A : Set ℓ} -> A -> (R : Rel A i) -> SetQuot R
    q[ x ]/ R = q[ x ]

    -- This tiny definition is the key to the whole development (look at where
    -- it is used below in `from`).  Free R can be thought of as R with extra edges added to make 
    -- it an equivalence relation.  When we pass q=-EqvRel to a Free R, we "interpret" those edges
    -- as equalities in SetQuot R, which might not immediately follow from quot-rel (e.g.
    -- it might take a few quot-rel's and transitivity). The fact that those edges can always be
    -- interepreted in SetQuot R comes from the fact that quot-rel's codomain is an equivalence 
    -- relation.
    q=-EqvRel : ∀ {ℓ i} {A : Set ℓ} {R : Rel A i} 
             -> EqvRel (\x y -> q[ x ]/ R == q[ y ]/ R)
    q=-EqvRel = record
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
  SetQuot-preserves-closure : ∀ {ℓ} {i} {A : Set ℓ} {R : Rel A i} 
                           -> SetQuot R ≃ SetQuot (Free (lmax ℓ i) R)
  SetQuot-preserves-closure {ℓ} {i} {A} {R} = equiv to from to-from from-to
    where
    to : SetQuot R -> SetQuot (Free (lmax ℓ i) R)
    to = SetQuot-rec {B = SetQuot (Free (lmax ℓ i) R)} SetQuot-level (\x -> q[ x ]) 
            (\rxy -> quot-rel (Free.Free-subrel rxy))
  
    from : SetQuot (Free (lmax ℓ i) R) -> SetQuot R
    from = SetQuot-rec {B = SetQuot R} SetQuot-level (\x -> q[ x ])
             (\freerxy -> freerxy _ q=-EqvRel quot-rel )

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
