{-# OPTIONS --without-K --rewriting #-}

module boolspace where

open import HoTT

-- "Simplified Inspect on Steroids"
record Reveal_·_is_ {a b} {A : Set a} {B : A -> Set b}
                    (f : (x : A) -> B x) (x : A) (y : B x) :
                    Set (lmax a b) where
  constructor r[_]
  field eq : f x == y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = r[ idp ]

Σ-prop-det : ∀ {i} {j} {A : Set i} {B : A -> Set j} -> Π A (is-prop ∘ B) -> {a b : Σ A B} -> fst a == fst b -> a == b
Σ-prop-det prop {a} {b} idp = pair= idp (prop-has-all-paths (prop (fst b)) _ _)

-- Agda can't seem to normalize this term.
bug : ∀ {i} {j} {A : Set i} {B : Set j} -> {e e' : A ≃ B} -> fst e == fst e' -> e == e'
bug = Σ-prop-det (\_ -> is-equiv-is-prop)


ua-ide : ∀ {ℓ} {A : Set ℓ} -> ua (ide A) == idp
ua-ide {_} {A} = ap ua idp ∙ ua-η _

ua-⁻¹ : ∀ {ℓ} {A B : Set ℓ} {e : A ≃ B} -> ua (e ⁻¹) == ! (ua e)
ua-⁻¹ = equiv-induction (\e' -> ua (e' ⁻¹) == ! (ua e')) (\A -> ap ua flipit ∙ ua-ide ∙ ap ! (! ua-ide)) _
  where
  flipit : ∀ {ℓ} {A : Set ℓ} -> ide A ⁻¹ == ide A
  flipit = Σ-prop-det (\_ -> is-equiv-is-prop) idp

not : Bool -> Bool
not true = false
not false = true

not-is-equiv : is-equiv not
not-is-equiv = is-eq not not (\{ true -> idp ; false -> idp }) (\{ true -> idp ; false -> idp })

not-equiv : Bool ≃ Bool
not-equiv = not , not-is-equiv

reverse-not-equiv : not-equiv ⁻¹ == not-equiv
reverse-not-equiv = Σ-prop-det (\_ -> is-equiv-is-prop) idp

Bool=Bool-not : Bool == Bool
Bool=Bool-not = ua not-equiv

Bool-has-distinct-paths : Bool=Bool-not ≠ idp
Bool-has-distinct-paths pp = Bool-false≠true (! follow-not ∙ ap follow pp)
  where
  follow : Bool == Bool -> Bool
  follow p = coe p true

  follow-not : follow Bool=Bool-not == false
  follow-not = coe-β not-equiv true

pair=-prop : ∀ {i j} {A : Set i} {B : A -> Set j}
      -> ((x : A) -> is-prop (B x))
      -> {x y : A} {bx : B x} {by : B y}
      -> x == y -> (x , bx) == (y , by)
pair=-prop prop idp = pair= idp (prop-has-all-paths (prop _) _ _ )

equiv-ext : ∀ {ℓ} {A B : Set ℓ} (f g : A ≃ B) -> –> f == –> g -> f == g
equiv-ext (f , f-is-equiv) (g , g-is-equiv) p = pair=-prop (\_ -> is-equiv-is-prop) p


Bool-induce-ide : (e : Bool ≃ Bool) -> –> e true == true -> e == ide Bool
Bool-induce-ide e p-true = equiv-ext e (ide Bool) –>e-is-idf
  where
  p-false : –> e false == false
  p-false with –> e false | inspect (–> e) false
  ...        | true | r[ eq ] = ⊥-rec (Bool-false≠true (! (<–-inv-l e _) ∙ ap (<– e) (eq ∙ ! p-true) ∙ <–-inv-l e _))
  ...        | false | _ = idp

  –>e-is-idf : –> e == idf Bool
  –>e-is-idf = λ= \{ true -> p-true ; false -> p-false }

Bool-induce-not : (e : Bool ≃ Bool) -> –> e true == false -> e == not-equiv
Bool-induce-not e p-true = equiv-ext e (not-equiv) –>e-is-not
  where
  p-false : –> e false == true
  p-false with –> e false | inspect (–> e) false
  ...        | true | _ = idp
  ...        | false | r[ eq ] = ⊥-rec (Bool-true≠false (! (<–-inv-l e _) ∙ ap (<– e) (p-true ∙ ! eq) ∙ <–-inv-l e _))

  –>e-is-not : –> e == not
  –>e-is-not = λ= \{ true -> p-true ; false -> p-false }

Bool-two-equivs : (e : Bool ≃ Bool) -> (e == ide Bool) ⊔ (e == not-equiv)
Bool-two-equivs e with –> e true | inspect (–> e) true 
...                  | true  | r[ eq ] = inl (Bool-induce-ide e eq)
...                  | false | r[ eq ] = inr (Bool-induce-not e eq)

_+++_ : ∀ {i i' j j'} {A : Set i} {A' : Set i'} {B : Set j} {B' : Set j'}
    -> (A -> A') -> (B -> B') -> A ⊔ B -> A' ⊔ B'
(f +++ g) (inl x) = inl (f x)
(f +++ g) (inr y) = inr (g y)

Bool-two-paths : (p : Bool == Bool) -> (p == idp) ⊔ (p == Bool=Bool-not)
Bool-two-paths p = (((_∙ lemma-ide-idp) ∘ lemma) +++ lemma) $ Bool-two-equivs (coe-equiv p)
  where
  lemma : {e : Bool ≃ Bool} -> coe-equiv p == e -> p == ua e
  lemma {e} q = ! (<–-inv-r ua-equiv p) ∙ ap ua q

  lemma-ide-idp : ∀ {ℓ} {A : Set ℓ} -> ua (ide A) == idp
  lemma-ide-idp = ap ua idp ∙ <–-inv-r ua-equiv idp

-- Just for fun:
Bool≃Bool=Bool : Bool ≃ (Bool == Bool)
Bool≃Bool=Bool = equiv to from to-from from-to
  where
  to : Bool -> Bool == Bool
  to true = idp
  to false = Bool=Bool-not

  from : Bool == Bool -> Bool
  from p with Bool-two-paths p
  ...       | inl _ = true
  ...       | inr _ = false

  to-from : ∀ p -> to (from p) == p
  to-from p with Bool-two-paths p
  ...       | inl q = ! q
  ...       | inr q = ! q

  from-to : ∀ b -> from (to b) == b
  from-to true = idp
  from-to false with Bool-two-paths Bool=Bool-not
  ...              | inl q = ⊥-rec (Bool-has-distinct-paths q)
  ...              | inr q = idp

Bool=Bool-is-set : is-set (Bool == Bool)
Bool=Bool-is-set = equiv-preserves-level Bool≃Bool=Bool Bool-is-set

-- I'm trying to construct a type with only one element but more than one
-- path without using HITs. I'm having trouble; maybe it's impossible, but I
-- don't know how I would show that.

-- I think this type might.  There's only one observable value of this type
-- but there ought to be two paths.

P2 = Σ Set (\A -> A == Bool)
baseP2 : P2
baseP2 = Bool , idp
path-to-baseP2 : (x : P2) -> x == baseP2
path-to-baseP2 (A , idp) = idp

=-emap-l : ∀ {ℓ} {X Y Z : Set ℓ} -> X ≃ Y -> (X == Z) ≃ (Y == Z)
=-emap-l {_} {X} {Y} {Z} e = equiv to from to-from from-to
  where
  to : X == Z -> Y == Z
  to p = ! (ua e) ∙ p

  from : Y == Z -> X == Z
  from p = ua e ∙ p

  to-from : ∀ p -> to (from p) == p
  to-from idp = ap (! (ua e) ∙_) (∙-unit-r _) ∙ !-inv-l (ua e)
  
  from-to : ∀ p -> from (to p) == p
  from-to idp = ap (ua e ∙_) (∙-unit-r _) ∙ !-inv-r (ua e)

=-emap-l-ide : ∀ {ℓ} {X Z : Set ℓ} -> =-emap-l (ide X) == ide (X == Z)
=-emap-l-ide = Σ-prop-det (\_ -> is-equiv-is-prop) (λ= (\p -> ap (\ □ -> ! □ ∙ p) ua-ide))


=-emap-ua-commute : {X Y Z : Set} {e : X ≃ Y} -> ap (\A -> A == Z) (ua e) == ua (=-emap-l e)
=-emap-ua-commute {Z = Z} {e = e} = equiv-induction (\e' -> ap (\A -> A == Z) (ua e') == ua (=-emap-l e')) 
                                     (\A -> ap (ap (_== Z)) ua-ide ∙ ! ua-ide ∙ ap ua (! =-emap-l-ide)) e

-- coe-equiv (ua (ide A)) == ide A

-- ua (ide A) == idp

counterexample : transport (\A -> A == Bool) (ua not-equiv) idp == Bool=Bool-not
counterexample = ap (\ □ -> coe □ idp) =-emap-ua-commute ∙ coe-β (=-emap-l not-equiv) _ ∙ ∙-unit-r (! Bool=Bool-not) ∙ ! ua-⁻¹ ∙ ap ua reverse-not-equiv

-- This tells us that we baseP2 = (Bool , idp), when we apply Bool=Bool-not to the first arg, we get Bool=Bool-not in the second arg.
-- IOW, 

path-in-P2 : (Bool , Bool=Bool-not) == baseP2
path-in-P2 = ! (pair= Bool=Bool-not (from-transp _ _ counterexample))

-- But, like, of course it is because all P2s are equal from path-to-baseP2.

-- Anyway, the nontrivial path I'm looking for, baseP2 == baseP2, probably does not exist because

no-idp-loop-for-not-path : idp == idp [ (_== Bool) ↓ Bool=Bool-not ] -> ⊥
no-idp-loop-for-not-path p = Bool-has-distinct-paths (! counterexample ∙ to-transp p)

-- Oh, yep, here we go.  It doesn't.  Darn.

baseP2-loopspace-is-contr : is-contr (baseP2 == baseP2)
baseP2-loopspace-is-contr = idp , lemma
  where
  lemma : {b : P2} (p : b == baseP2) -> path-to-baseP2 b == p
  lemma idp = idp

-- Here's a question
question : path-to-baseP2 _ == path-in-P2
question = {! !}


