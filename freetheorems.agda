{-# OPTIONS --without-K --type-in-type --rewriting #-}

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

cons-replicate : {n : Nat} {A : Set} {x : A} {m : Fin (S n)} -> cons x (replicate {n = n} x) m == replicate x m
cons-replicate {m = O , p} = idp
cons-replicate {m = S m , p} = idp

<-antisym : {n : Nat} -> ¬ (n < n)
<-antisym {O} ()
<-antisym {S n} p = <-antisym (<-cancel-S p)

Σ-mere-prop-eq : {A : Set} {F : A -> Set} -> ((x : A) -> has-all-paths (F x)) -> (a b : Σ A F) -> fst a == fst b -> a == b
Σ-mere-prop-eq f (a1 , a2) (.a1 , b2) idp = pair= idp (f a1 a2 b2)

Fin-eq : {n : ℕ} -> (a b : Fin n) -> fst a == fst b -> a == b
Fin-eq = Σ-mere-prop-eq (\x -> <-has-all-paths)

Fin-contr : {n : ℕ} -> (a b : Fin n) -> fst a == fst b -> is-contr (a == b)
Fin-contr a b p = Fin-eq a b p , (\q -> prop-has-all-paths (Fin-is-set a b) (Fin-eq a b p) q)

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

diagEnvR : {n : Nat} (env : Vector n Set) (i : Fin n) -> Rel (env i) (env i)
diagEnvR envA i = _==_

addEnvR-const-diag : {n : Nat} (env : Vector n Set) (A : Set) -> addEnvR (_==_ {_} {A}) (diagEnvR env) == diagEnvR (cons A env)
addEnvR-const-diag env A = λ= \{ (O , p) -> idp ; (S i , p) -> idp }

relType : {n : Nat} {envA envB : Vector n Set} (envR : (i : Fin n) -> Rel (envA i) (envB i)) (t : TypeExp n) -> Rel (evalType envA t) (evalType envB t)
relType envR boolT = Discrete Bool
relType envR (arrowT t u) = relType envR t ~> relType envR u
relType envR (forAllT t) = Λ (\r -> relType (addEnvR r envR) t)
relType envR (varT n) = envR n


rel-is-eq : {n : Nat} (env : Vector n Set) (t : TypeExp n)
         -> relType (diagEnvR env) t == _==_
rel-is-eq _ boolT = idp
rel-is-eq env (arrowT t u) = transport! (\ □ -> □ ~> relType (\_ -> _==_) u == _==_) (rel-is-eq env t)
                            (transport! (\ □ -> _==_ ~> □ == _==_) (rel-is-eq env u)
                             EqPreserving.~>-preserves-eq)
rel-is-eq env (forAllT t) = λ= \f -> λ= \g -> ua eqv
  where
  eqv : ∀ {n} {env : Fin n → Set}
        {t : TypeExp (S n)} {f g : ∀ x → evalType (cons x env) t} →
        Λ (\R -> relType (addEnvR R (\_ -> _==_)) t) f g ≃ (f == g)
  eqv {env = env} {t = t} {f = f} {g = g} = (\k -> λ= \X ->
     let step1 = k X X _==_ 
         step2 = transport (\ □ -> relType □ t (f X) (g X)) (addEnvR-const-diag env X) step1
         step3 = transport (\ □ -> □ (f X) (g X)) (rel-is-eq (cons X env) t) step2
      in step3) , is-eq _ (\p -> transport! (\ □ -> Λ (\R -> relType (addEnvR R (diagEnvR env)) t) □ g) p 
                                 {!!}) 
                          {!!} {!!}
rel-is-eq env (varT x) = idp

{-
{-
FreeTheorem : TypeExp O -> Set
FreeTheorem t = (x : evalType nilV t) -> relType (\{ (_ , ()) }) t t x x

all-free-theorems : (t : TypeExp O) -> FreeTheorem t
all-free-theorems boolT x = idp
all-free-theorems (arrowT t u) f a b r = {!!}
all-free-theorems (forAllT t) x R = {!!}
all-free-theorems (varT x) x₁ = {!!}
-}

-}
