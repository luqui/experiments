{-# OPTIONS --without-K --type-in-type #-}

module freetheorems where

open import HoTT hiding (Rel)
open import lib.Funext

Rel : Set -> Set -> Set
Rel A B = A -> B -> Set

-- Combinators for building types-as-relations.
Discrete : (A : Set) -> Rel A A
Discrete _ x y = x == y

Eq : (A : Set) -> Rel A A
Eq A = _==_



infixr 50 _~>_
_~>_ : {A A' B B' : Set} -> Rel A A' -> Rel B B' -> Rel (A -> B) (A' -> B')
(Ra ~> Rb) f g = ∀ x y -> Ra x y -> Rb (f x) (g y)

_<×>_ : {A A' B B' : Set} -> Rel A A' -> Rel B B' -> Rel (A × B) (A' × B')
(Ra <×> Rb) (a , b) (a' , b') = Ra a a' × Rb b b'

_<⊔>_ : {A A' B B' : Set} -> Rel A A' -> Rel B B' -> Rel (A ⊔ B) (A' ⊔ B')
(Ra <⊔> Rb) (inl a) (inl a') = Ra a a'
(Ra <⊔> Rb) (inr b) (inr b') = Rb b b'
(Ra <⊔> Rb) _ _ = ⊥

Λ : {F F' : Set -> Set} -> ({A A' : Set} -> Rel A A' -> Rel (F A) (F' A')) -> Rel (Π Set F) (Π Set F')
Λ F f g = (A A' : Set) (R : Rel A A') -> F R (f A) (g A')

module EqPreserving where
  private 
    lemma : {A B : Set} {f g : A -> B}
          -> (p : (x y : A) -> (x == y) -> f x == g y)
          -> {z z' : A} (q : z == z')
          -> ap f q ∙ app= (λ= (λ x → p x x idp)) z' == p z z' q
    lemma p idp = app=-β _ _

  ~>-preserves-eq : {A B : Set} -> (Eq A ~> Eq B) == Eq (A -> B)
  ~>-preserves-eq = λ= (\f -> λ= (\g -> 
     ua ( (\r -> λ= (\x -> r x x idp))
        , is-eq _ (\p -> \_ _ q -> ap f q ∙ app= p _)
                  (\b -> ! (λ=-η b))
                  (\a -> λ= (\z -> λ= (\z' -> λ= (\q -> lemma a q)))))))

  ×-preserves-eq : {A B : Set} -> (Eq A <×> Eq B) == Eq (A × B)
  ×-preserves-eq = λ= (\{ (x , y) -> λ= (\{ (x' , y') -> 
    ua ( (\{ (p , q) -> pair×= p q })
       , is-eq _ (\p -> fst×= p , snd×= p)
                 (\b -> ! (pair×=-η b) )
                 (\{ (xp , yp) -> pair×= (fst×=-β xp yp) (snd×=-β xp yp) })) })})


  Reflexive : {A : Set} -> Rel A A -> Set
  Reflexive {A} R = (x : A) -> R x x


  -- P is a natural transformation Id -> F, where the categories are squared.
  -- That is, P . f = F f . P.
{-
  Λ-preserves-eq : {F : Set -> Set} {P : {A A' : Set} -> Rel A A' -> Rel (F A) (F A')}
                -> ({A : Set} -> P (Eq A) == Eq (F A))
                -> Λ P == Eq (Π Set F)
  Λ-preserves-eq ind = λ= (\f -> λ= (\g -> 
     ua ( (\r -> λ= (\x -> coe (app= (app= ind (f x)) (g x)) (r x x (Eq x))))
        , is-eq _ {!!}
                  {!!}
                  {!!})))
-}

data TypeExp : Nat -> Set where
  boolT : {n : Nat} -> TypeExp n
  arrowT : {n : Nat} -> TypeExp n -> TypeExp n -> TypeExp n
  forAllT : {n : Nat} -> TypeExp (S n) -> TypeExp n
  varT : {n : Nat} -> Fin n -> TypeExp n

Vector : Nat -> Set -> Set
Vector n A = Fin n -> A

nilV : {A : Set} -> Vector O A
nilV (n , ())

cons : {A : Set} {n : Nat} -> A -> Vector n A -> Vector (S n) A
cons x xs (O , p) = x
cons x xs (S n , p) = xs (n , <-cancel-S p)

replicate : {A : Set} {n : Nat} (x : A) -> Vector n A
replicate x _ = x

cons-replicate : {n : Nat} {A : Set} {x : A} -> cons x (replicate {n = n} x) == replicate x
cons-replicate = λ= (\{ (O , p) -> idp ; (S n , p) -> idp })

<-antisym : {n : Nat} -> ¬ (n < n)
<-antisym {O} ()
<-antisym {S n} p = <-antisym (<-cancel-S p)

absurd : {A : Set} -> ⊥ -> A
absurd ()


<-rec : {n : Nat}
     -> (P : {m : Nat} -> n < m -> Set)
     -> P ltS
     -> ({m : Nat} {q : n < m} -> P q -> P (ltSR q)) 
     -> {m : Nat} (p : n < m) -> P p
<-rec P lts ltsr ltS = lts
<-rec P lts ltsr (ltSR p) = ltsr (<-rec P lts ltsr p)

-- Ugh we have to reimplement a lot of < functions because they were marked abstract
-- for some reason.
<-trans' : {m n k : ℕ} → m < n → n < k → m < k
<-trans' lt₁ ltS = ltSR lt₁
<-trans' lt₁ (ltSR lt₂) = ltSR (<-trans' lt₁ lt₂)

<-ap-S' : {m n : ℕ} → m < n → S m < S n
<-ap-S' ltS = ltS
<-ap-S' (ltSR lt) = ltSR (<-ap-S' lt)

<-cancel-S' : {m n : ℕ} → S m < S n → m < n
<-cancel-S' ltS = ltS
<-cancel-S' (ltSR lt) = <-trans' ltS lt  

n-Sn-has-all-paths : {n : Nat} -> has-all-paths (n < S n)
n-Sn-has-all-paths {O} ltS ltS = idp
n-Sn-has-all-paths {O} ltS (ltSR ())
n-Sn-has-all-paths {O} (ltSR ()) q
n-Sn-has-all-paths {S n} p q 
  = let r = n-Sn-has-all-paths (<-cancel-S' p) (<-cancel-S' q) 
     in ! (<-cancel-S-ap p) ∙ ap (<-ap-S') r ∙ <-cancel-S-ap q
  where
  this-is-getting-ridiculous : {m n : Nat} (p : S m < n) -> <-ap-S' (<-trans' ltS p) == ltSR p
  this-is-getting-ridiculous ltS = idp
  this-is-getting-ridiculous (ltSR p) = ap ltSR (this-is-getting-ridiculous p)

  <-cancel-S-ap : {m n : Nat} -> (p : S m < S n) -> <-ap-S' (<-cancel-S' p) == p
  <-cancel-S-ap ltS = idp
  <-cancel-S-ap (ltSR p) = this-is-getting-ridiculous p

<-irrefl : {n : Nat} -> ¬ (n < n)
<-irrefl {O} ()
<-irrefl {S n} p = <-irrefl (<-cancel-S p)

<-is-mere-prop : {n n' : Nat} -> has-all-paths (n < n')
<-is-mere-prop {n} {O} () ()
<-is-mere-prop {.n'} {S n'} ltS q = n-Sn-has-all-paths ltS q
<-is-mere-prop {n} {S _} (ltSR p) ltS = absurd (<-irrefl p)
<-is-mere-prop {n} {S n'} (ltSR p) (ltSR q) = ap ltSR (<-is-mere-prop p q)


Σ-mere-prop-eq : {A : Set} {F : A -> Set} -> ((x : A) -> has-all-paths (F x)) -> (a b : Σ A F) -> fst a == fst b -> a == b
Σ-mere-prop-eq f (a1 , a2) (.a1 , b2) idp = pair= idp (f a1 a2 b2)

Fin-eq : {n : ℕ} -> (a b : Fin n) -> fst a == fst b -> a == b
Fin-eq = Σ-mere-prop-eq (\x -> <-is-mere-prop {x})

evalType : {n : Nat} -> Vector n Set -> TypeExp n -> Set
evalType env boolT = Bool
evalType env (arrowT t u) = evalType env t -> evalType env u
evalType env (forAllT f) = Π Set (\A -> evalType (cons A env) f)
evalType env (varT n) = env n

addEnvR : {n : Nat} {envA envB : Vector n Set} {T T' : Set}
        -> Rel T T'
        -> ((i : Fin n) -> Rel (envA i) (envB i)) 
        -> ((i : Fin (S n)) -> Rel (cons T envA i) (cons T' envB i))
addEnvR r envR (O , p) = r
addEnvR r envR (S n , p) = envR (n , <-cancel-S p) 

lift-relation : {n : Nat} {T T' : Set} (R : Rel T T') (i : Fin (S n)) 
      -> Rel (cons T (replicate T) i) (cons T' (replicate T') i)
lift-relation {n} {T} {T'} R rewrite cons-replicate {n} {Set} {T}
                                   | cons-replicate {n} {Set} {T'}
   = \_ -> R

addEnvR-const : {n : Nat} {T T' : Set} {R : Rel T T'} 
            -> addEnvR {n} {replicate T} {replicate T'} R (\_ -> R) 
                == (lift-relation R)
addEnvR-const = {!!}

relType : {n  : Nat} {envA envB : Vector n Set} (envR : (i : Fin n) -> Rel (envA i) (envB i)) (tA : TypeExp n) (tB : TypeExp n) -> Rel (evalType envA tA) (evalType envB tB)
relType envR boolT boolT = Discrete Bool
relType envR (arrowT t u) (arrowT t' u') = relType envR t t' ~> relType envR u u'
relType envR (forAllT t) (forAllT t') = Λ (\r -> relType (addEnvR r envR) t t') 
relType {_} {envA} {envB} envR (varT n) (varT n')
                                   with ℕ-has-dec-eq (fst n) (fst n')
...                                | inl eq = transport (\i -> envA n -> envB i -> Set) (Fin-eq n n' eq) (envR n)
...                                | inr ne = \_ _ -> ⊥
relType _ _ _ _ _ = ⊥


rel-is-eq : {n : Nat} (env : Vector n Set) (t : TypeExp n)
         -> relType {_} {env} {env} (\_ -> _==_) t t == _==_
rel-is-eq _ boolT = idp
rel-is-eq env (arrowT t u)
  rewrite rel-is-eq env t | rel-is-eq env u = EqPreserving.~>-preserves-eq
rel-is-eq env (forAllT t) = {!!}
rel-is-eq env (varT x) with ℕ-has-dec-eq (fst x) (fst x)
...                          | inl eq = let eq-is-idp = fst (ℕ-is-set (fst x) (fst x) eq idp)
                                         in transport (\p -> transport (\i -> env x -> env i -> Set) (Fin-eq x x p) _==_ == _==_) (! eq-is-idp) {!idp!}
                    -- transport (\p -> transport _ p _ == _) eq-is-idp idp
...                          | inr ne = {!!}
-- ...                       | inl eq = {!!} -- rewrite (Fin-eq x x eq) = idp
-- ...                       | inr ne = absurd (ne idp)

{-
FreeTheorem : TypeExp O -> Set
FreeTheorem t = (x : evalType nilV t) -> relType (\{ (_ , ()) }) t t x x

all-free-theorems : (t : TypeExp O) -> FreeTheorem t
all-free-theorems boolT x = idp
all-free-theorems (arrowT t u) f a b r = {!!}
all-free-theorems (forAllT t) x R = {!!}
all-free-theorems (varT x) x₁ = {!!}
-}
