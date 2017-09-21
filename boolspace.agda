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


not : Bool -> Bool
not true = false
not false = true

not-is-equiv : is-equiv not
not-is-equiv = is-eq not not (\{ true -> idp ; false -> idp }) (\{ true -> idp ; false -> idp })

not-equiv : Bool ≃ Bool
not-equiv = not , not-is-equiv

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

-- I'm trying to construct a type with only one element but more than one
-- path without using HITs. I'm having trouble; maybe it's impossible, but I
-- don't know how I would show that.


-- Hmm, ok, what if we try a Scott encoding. We have this HIT:
--
-- data BoolSpace : Set where
--   base : BoolSpace
--   path : base == base
--
-- Its induction principle is:
--
-- BoolSpace-ind : {P : BoolSpace -> Set} -> (pbase : P base) -> pbase == pbase -> (b : BoolSpace) -> P b
--
-- Making a Scott encoding of this is pretty impossible.  What about its recursion principle?
--
-- BoolSpace-rec : {B : Set} (x : B) -> x == x -> BoolSpace -> B
--
-- Thus the Scott encoding:

BoolSpace = {B : Set} (x : B) -> x == x -> B

-- Let's study this type.
