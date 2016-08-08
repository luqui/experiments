{-# LANGUAGE DataKinds, PolyKinds, TypeOperators, TypeFamilies, UndecidableInstances #-}

-- c is a combination of multiplication and continuation.
-- Nested2 sums all (c x y) where x and y range over the iterations of i
-- (i can be thought of "increment").  So if c is multiplication, Nested2
-- will calculate the composites.  But c could also include a continuation
-- so that we could apply some function to the composites and sum over that.
data Nested2 c i x y
    = Leaf (c x y)
    | L (Nested2 c i (i x) y)
    | R (Nested2 c i x (i y))

-- The sum of all composites, with multiplicity.
-- E.g. 
-- 8 = Composite . L . L . Leaf   -- 4*2
--   = Composite . R . R . Leaf   -- 2*4
--
-- Composite = Σ{n} D(n), where D(n) is the number of nontrivial divisors of n.
-- (A070824)
newtype Composite = Composite { getComposite :: Nested2 (,) Maybe Bool Bool }


-- Now we'll do the same for repeated application of functors.
--   CompositeF f a = Σ{n} D(n) f^n(a) 
-- There's some type family stuff to make it easier to work with.
-- Try e.g. 
-- ghci> :t CompositeF . L . Leaf . CompCont
--   :: f (f (f (f (f (f a))))) -> CompositeF f a

data Nat = Zero | Succ Nat

type family Iter n f a where
    Iter Zero f a = a
    Iter (Succ n) f a = Iter n f (f a)

type family Plus a b where
    Plus Zero b = b
    Plus (Succ a) b = Succ (Plus a b)

type family Times a b where
    Times Zero b = Zero
    Times (Succ a) b = Plus b (Times a b)

type Two = Succ (Succ Zero)

newtype CompCont f a x y = CompCont { getCompCont :: Iter (Times x y) f a }
newtype CompositeF f a = CompositeF { 
        getCompositeF :: Nested2 (CompCont f a) Succ Two Two
}
