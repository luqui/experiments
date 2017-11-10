open import HoTT

swap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} -> (A -> B -> C) -> (B -> A -> C)
swap f x y = f y x

module foldlr {i} {A : Type i} where 
  foldl : ∀ {j} {B : Type j} -> (B -> A -> B) -> B -> List A -> B
  foldl f z nil = z
  foldl f z (x :: xs) = foldl f (f z x) xs

  module _ {j} {B : Type j} {f : A -> B -> B} where
    private
      foldl-snoc : {z : B} (x : A) (xs : List A) -> f x (foldl (swap f) z xs) == foldl (swap f) z (snoc xs x)
      foldl-snoc x nil = idp
      foldl-snoc x (y :: ys) = foldl-snoc x ys

    foldl-swap : (z : B) (xs : List A)
                -> foldr f z xs == foldl (swap f) z (reverse xs)
    foldl-swap z nil = idp
    foldl-swap z (x :: xs) = 
      foldr f z (x :: xs)                      =⟨ idp ⟩
      f x (foldr f z xs)                       =⟨ ap (f x) (foldl-swap z xs) ⟩
      f x (foldl (swap f) z (reverse xs))      =⟨ foldl-snoc x (reverse xs) ⟩
      foldl (swap f) z (snoc (reverse xs) x)   =⟨ idp ⟩
      foldl (swap f) z (reverse (x :: xs))     =∎ 

  module _ where
    private 
      go : List A -> List A -> List A
      go r nil = r
      go r (x :: xs) = go (x :: r) xs

      go-lemma : (r : List A) (xs : List A) -> go r xs == reverse xs ++ r
      go-lemma r nil = idp
      go-lemma r (x :: xs) = 
          go (x :: r) xs                       =⟨ go-lemma (x :: r) xs ⟩
          reverse xs ++ (x :: r)               =⟨ idp ⟩
          reverse xs ++ ((x :: nil) ++ r)      =⟨ ! (++-assoc (reverse xs) (x :: nil) r)  ⟩
          (reverse xs ++ (x :: nil)) ++ r      =⟨ idp ⟩
          snoc (reverse xs) x ++ r             =⟨ idp ⟩
          reverse (x :: xs) ++ r               =∎

    reverse' : List A -> List A
    reverse' = go nil

    reverse'=reverse : (xs : List A) -> reverse' xs == reverse xs
    reverse'=reverse xs = go-lemma nil xs ∙ ++-unit-r _
