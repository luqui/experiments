{-# OPTIONS --type-in-type #-}

-- Exploring the free theorems and church numerals.
-- The key result is that the following are equivalent:
--    - The type (X : Set) -> (X -> X) -> X -> X represents the church numerals exactly
--    - The free theorem for this type is true

module reltype where

open import Data.Empty
open import Data.Unit
open import Data.Maybe
open import Data.Bool using (Bool ; true ; false)
open import Data.Nat
open import Data.Product hiding (∃)
open import Data.Sum
open import Function using (id)
open import Relation.Nullary
import Level
open import Relation.Binary.PropositionalEquality

Rel : Set -> Set -> Set
Rel X Y = X -> Y -> Set

-- Combinators for building types-as-relations.
Discrete : (A : Set) -> Rel A A
Discrete _ x y = x ≡ y

record _≃_ (A B : Set) : Set where
  field
    f : A -> B
    g : B -> A
    f-g : ∀ b -> f (g b) ≡ b
    g-f : ∀ a -> g (f a) ≡ a

infixr 50 _~>_
_~>_ : {A A' B B' : Set} -> Rel A A' -> Rel B B' -> Rel (A -> B) (A' -> B')
(Ra ~> Rb) f g = ∀ x y -> Ra x y -> Rb (f x) (g y)

_<×>_ : {A A' B B' : Set} -> Rel A A' -> Rel B B' -> Rel (A × B) (A' × B')
(Ra <×> Rb) (a , b) (a' , b') = Ra a a' × Rb b b'

_<⊎>_ : {A A' B B' : Set} -> Rel A A' -> Rel B B' -> Rel (A ⊎ B) (A' ⊎ B')
(Ra <⊎> Rb) (inj₁ a) (inj₁ a') = Ra a a'
(Ra <⊎> Rb) (inj₂ b) (inj₂ b') = Rb b b'
(Ra <⊎> Rb) _ _ = ⊥

Π : {A : Set} -> (A -> Set) -> Set
Π {A} F = (x : A) -> F x

Λ : {F F' : Set -> Set} -> ({A A' : Set} -> Rel A A' -> Rel (F A) (F' A')) -> Rel (Π F) (Π F')
Λ F f g = {A A' : Set} -> (R : Rel A A') -> F R (f A) (g A')

-- (A guess at this definition)
∃ : {F F' : Set -> Set} -> ({A A' : Set} -> Rel A A' -> Rel (F A) (F' A')) -> Rel (Σ Set F) (Σ Set F')
∃ F (A , x) (A' , y) = Σ (Rel A A') (\R -> F R x y)


FreeTheorem : {A : Set} -> Rel A A -> Set
FreeTheorem R = ∀ f -> R f f


-- Warm up: the only function of type (X : Set) -> X -> X  is the identity.
poly-id-theorem : FreeTheorem (Λ (\X -> X ~> X)) -> (f : (A : Set) -> A -> A) (A : Set) (x : A) -> f A x ≡ x
poly-id-theorem thm f A x = thm f (\y _ -> y ≡ x) x x refl





-- Now let's do church numerals.

ChurchNum : Set
ChurchNum = (X : Set) -> (X -> X) -> (X -> X)

-- This is just for reference, and better variable names.  FreeTheorem, as we see below, takes care of generating it.
ChurchNumTheorem : Set
ChurchNumTheorem = (f : ChurchNum)
                -> {A B : Set} (R : A -> B -> Set)
                -> (μ : A -> A) (ν : B -> B)
                -> ((x : A) (y : B) -> R x y -> R (μ x) (ν y))
                -> (x : A) (y : B) -> R x y -> R (f A μ x) (f B ν y)

church-num-theorem-verify : ChurchNumTheorem ≡ FreeTheorem (Λ (\X -> (X ~> X) ~> (X ~> X)))
church-num-theorem-verify = refl

-- Specializing to a unary relation ("induction") is also helpful.
ChurchNumTheoremSimple : Set
ChurchNumTheoremSimple = (f : ChurchNum)
                         {A : Set} (R : A -> Set)
                         (μ : A -> A) ->
                         ((x : A) -> R x -> R (μ x)) ->
                         (x : A) -> R x -> R (f A μ x)

fpow : {A : Set} -> ℕ -> (A -> A) -> (A -> A)
fpow zero _ x = x
fpow (suc n) f x = f (fpow n f x)

fpow-nat : (n : ℕ) -> fpow n suc zero ≡ n
fpow-nat zero = refl
fpow-nat (suc n) = cong suc (fpow-nat n)

record Orbit {A : Set} (μ : A -> A) (x0 : A) (y : A) : Set where
  field
    n : ℕ
    orbit : y ≡ fpow n μ x0

-- Here we show that the church numerals are exactly finite repeated applications of a function.
module ChurchNums (freethm : ChurchNumTheorem) (f : ChurchNum) where
  simplethm : ChurchNumTheoremSimple
  simplethm f R μ ind x rx = freethm f (\x tt -> R x) μ (\t -> t) (\x _ r -> ind x r) x tt rx

  generalization : (n : ℕ) -> f ℕ suc zero ≡ n
                -> {A : Set} (μ : A -> A) (x0 : A)
                -> f A μ x0 ≡ fpow n μ x0
  generalization n p μ x0 = 
    let r = freethm f (\a n' -> a ≡ fpow n' μ x0) μ suc (\x y -> cong μ) x0 zero refl 
    in subst (\ □ -> f _ μ x0 ≡ fpow □ μ x0) p r

  find-orbit : {A : Set} (μ : A -> A)
            -> (x0 : A) -> Orbit μ x0 (f A μ x0)
  find-orbit {A} μ x0 = simplethm f (Orbit μ x0) μ ind x0 basecase
    where
    basecase = record { n = zero ; orbit = refl }
    ind : (x : A) -> Orbit μ x0 x -> Orbit μ x0 (μ x)
    ind x orb = record { n = suc (Orbit.n orb) ; orbit = cong μ (Orbit.orbit orb) }

  characterization : Extensionality Level.zero Level.zero
                  -> Σ ℕ (\n -> f ≡ (\X -> fpow n))
  characterization ex =
    let orb = find-orbit suc zero
    in Orbit.n orb , ex (\X -> ex (\μ -> ex (\x0 -> generalization (Orbit.n orb) (trans (Orbit.orbit orb) (fpow-nat _)) μ x0)))

-- And here we show that this characterization is sufficient to have the free theorem, establishing equivalence.
reverse-characterization : ((f : ChurchNum) -> Σ ℕ (\n -> f ≡ (\X -> fpow n))) -> ChurchNumTheorem
reverse-characterization char f R μ ν ind x y r0 
      with char f
...      | n , p rewrite p = fpow-induction n
  where
  fpow-induction : (n : ℕ) -> R (fpow n μ x) (fpow n ν y)
  fpow-induction zero = r0
  fpow-induction (suc n) = ind _ _ (fpow-induction n)



-- Some existential play.  From the conclusions here it seems likely that free theorems involving
-- existentials are not true in Agda, though they seem like they would be true in a weaker
-- type system.  But since existentials are isomorphic to their rank-2 eliminators, it makes
-- me think that those free theorems are probably false, too.  Something to explore later.

ExContext : Set -> Set
ExContext A = Σ Set (\X -> X × (X -> A))

ExContextRel : (A : Set) -> Rel (ExContext A) (ExContext A)
ExContextRel A = ∃ (\X -> X <×> (X ~> Discrete A))


ExContextTheorem : Set -> Set
ExContextTheorem A = (EX : ExContext A) -> let X , x , f = EX 
                  in Σ (X -> X -> Set) (\R ->
                     (R x x) × ((a b : X) -> R a b -> f a ≡ f b))

ex-context-theorem-verify : (A : Set) -> ExContextTheorem A ≡ FreeTheorem (ExContextRel A)
ex-context-theorem-verify A = refl

-- This theorem is boring, doesn't tell us anything.
ex-context-theorem-true : (A : Set) -> ExContextTheorem A
ex-context-theorem-true A (X , x , f) = _≡_ , refl , (\_ _ -> cong f)

-- Maybe we get the interesting results from *eliminating* an ExContext?

ExContextElimRel : (A : Set) {B B' : Set} -> Rel B B' -> Rel (ExContext A -> B) (ExContext A -> B')
ExContextElimRel A RB = ExContextRel A ~> RB


ExContextElimTheorem : Set -> {B : Set} -> Rel B B -> Set
ExContextElimTheorem A {B} RB = (f : ExContext A -> B)
                         -> (CX CY : ExContext A)
                         -> let (X , x , xf) = CX
                                (Y , y , yf) = CY
                         in Σ (Rel X Y) (\R ->
                           (R x y) × ((x' : X) (y' : Y) -> R x' y' -> xf x' ≡ yf y'))
                         -> RB (f CX) (f CY)

 
ex-context-elim-theorem-verify : (A B : Set) (RB : Rel B B) -> ExContextElimTheorem A RB ≡ FreeTheorem (ExContextElimRel A RB)
ex-context-elim-theorem-verify _ _ _ = refl

module ExContexts (A : Set) (freethm : (B : Set) (RB : Rel B B) -> ExContextElimTheorem A RB) where
  toA : ExContext A -> A
  toA (X , x , f) = f x

  fromA : A -> ExContext A
  fromA a = A , a , id

  bij1 : (a : A) -> toA (fromA a) ≡ a
  bij1 a = refl

{-
  bij2-lemma : (B : Set) (f : ExContext A -> B) (ex : ExContext A) -> f (fromA (toA ex)) ≡ f ex
  bij2-lemma B f ex = 
    let X , x , xf = fromA (toA ex)
        Y , y , yf = ex
    in
    freethm B f (fromA (toA ex)) ex ((\x y -> xf x ≡ yf y) , refl , (\x' y' p -> p))

  bij2 : (ex : ExContext A) -> fromA (toA ex) ≡ ex
  bij2 ex = bij2-lemma (ExContext A) id ex

-- Here we see that Agda and ExContextElimTheorem are incompatible, because Agda can look inside existentials.
ex-context-elim-contradiction : ((A B : Set) -> ExContextElimTheorem A B) -> ⊥ 
ex-context-elim-contradiction freethm = ⊤-not-Bool (cong proj₁ (ExContexts.bij2 ⊤ (freethm ⊤) (Bool , true , \_ -> tt)))
  where
  all-⊤-equal : (x y : ⊤) -> x ≡ y
  all-⊤-equal tt tt = refl

  ⊤-not-Bool : ⊤ ≡ Bool -> ⊥
  ⊤-not-Bool p with subst (\ □ -> (x y : □) -> x ≡ y) p all-⊤-equal true false
  ...             | ()
-}


module SigmaAsPi (A : Set) (F : A -> Set) (ex : Extensionality _ _) where
   PiRepr = (Z : Set) -> ((x : A) -> F x -> Z) -> Z

   toPiRepr : Σ A F -> PiRepr
   toPiRepr (x , y) Z elim = elim x y

   fromPiRepr : PiRepr -> Σ A F
   fromPiRepr r = r (Σ A F) (\x y -> (x , y))

   bij1 : (p : Σ A F) -> fromPiRepr (toPiRepr p) ≡ p
   bij1 p = refl

   bij2 : (r : PiRepr) -> toPiRepr (fromPiRepr r) ≡ r
   bij2 r = ex (\x -> ex (\elim -> {!!}))


-- -- Dependent types mess up standard parametricity, because terms can depend on types.  So even with
-- -- Type's relation being equivalence/equality, we can get nonsense.
-- Type : Rel Set Set
-- Type X Y = X ≃ Y
-- badΛ : FreeTheorem (Λ (\_ -> Type)) -> ⊥
-- badΛ freethm = _≃_.f (freethm (\x -> x) {⊤} {⊥} (\_ _ -> ⊤)) tt
-- -- Parhaps Λ needs an extra condition. 

Type : Rel Set Set
Type X Y = X ≃ Y
Λ' : {F F' : Set -> Set} -> Rel Set Set -> ({A A' : Set} -> Rel A A' -> Rel (F A) (F' A')) -> Rel (Π F) (Π F')
Λ' R F f g = {A A' : Set} -> R A A' -> (R : Rel A A') -> F R (f A) (g A')

-- This weakened Λ' often gives consequences of univalence... always?  Possibly always.  Functions that return 
-- types cannot be considered parametric.  I guess parametricity is really about type erasure: that type
-- information will never enter term space.  It might be mathematically sufficient to declare that functions to
-- Bool or Nat are always parametric, though massaging that into a form that could be useful for reasoning
-- might be a challenge.

-- It makes me think of "parametricity levels" similar to homotopy levels.  Like, if you quantify over something,
-- what is its reach.  E.g. Quantifying over Set₁ into Set should also have a parametricity law.  
-- In fact, I wonder if that would happen naturally, and my above counterexample was actually just using
-- --type-in-type to find its contradiction.

-- What if the const rule were enough:
--
--   (*) (ΛX. X -> Y) ≃ Y
--        f   x = x ⊤ tt
--        f⁻¹ y = (\_ _ -> y)
--
-- Given two functions f g : ΛX. X -> X
-- 
-- Define h : Λ(X : Set₁). X -> Set
--        h X x = f X x ≡ g X x
--
-- The (universe-corrected) const rule gives us
--
--        e : (Λ(X : Set₁). X -> Set) ≃ Set
--
-- Let A : Set₁ and a : A.
--
-- e⁻¹ (e h) A a = e⁻¹ (h ⊤ tt) A a
--               = e⁻¹ (f ⊤ tt ≡ g ⊤ tt) A a
--               = e⁻¹ (tt ≡ tt) A a     -- by ⊤ contractible
--               = tt ≡ tt
--
-- But ALSO
--
-- e⁻¹ (e h) A a = (e⁻¹ ∘ e) h A a
--               = idf h A a
--               = h A a
--               = f A a ≡ g A a
--
-- Thus by transporting refl : tt ≡ tt along this equivalence, we show that f A a ≡ g A a, as
-- long as is in at least universe Set₁ (because we used the const rule at universe Set).
--
-- 
