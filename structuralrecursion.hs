{-# LANGUAGE DeriveFunctor, ExistentialQuantification #-}

-- A structurally recursive function f :: [a] -> b is isomorphic to a list
-- fold, which can be incrementalized as (a -> b -> b, b).  Any function which
-- consumes [a] in a structurally recursive way (but does not necessarily use its
-- own result recursively) can be incrementalized on the structural part; that is:
-- ∃ s. (a -> s -> s, s, s -> b)

-- LF a b = list function = [a] -> b
data LF a b = forall s. LF (a -> s -> s) s (s -> b)

-- We generalize this to any recursive structure

newtype Mu f = Roll { unroll :: f (Mu f) }

-- MF b = mu function = Mu f -> b
data MF f b = forall s. MF (f s -> s) (s -> b)


-- (x:xs, y:ys) has an unusual structure
--
--         (x:xs, y:ys)
--        /            \
--   (xs, y:ys)     (x:xs, ys)
--        \           /
--           (xs, ys)

-- merge :: (Ord a) => [a] -> [a] -> [a] is structurally recursive in this way. 
-- It should be easy to incrementally compute an update (prepend) to either list.

-- L2F a b c = [a] * [b] -> c
data L2F a b c = 
    forall s. L2F (LF b s)   -- left empty 
                  (LF a s)   -- right empty
                  (a -> b -> s -> s -> s) -- left sub, right sub
                  (s -> c)

{-

The point is to tag every point in the structural tree with an s.  Products
have interesting tree (well, dag) structures.

                        [1,2],[3,4]
                      /             \
               [2],[3,4]         [1,2],[4]
              /       \         /         \
        [],[3,4]        [2],[4]           [1,2],[]
              \       /         \        /
                [],[4]            [2],[]
                      \         /
                           []

-}

-- So L2F can be folded naively (like a tree) or smartly (like this dag).  It's
-- up to the consumer, offering the possibility for more composable efficiency than
-- before.
--
-- Now the questions are: how do we compute L2F from its components, and how do we
-- make computing on the structure above easy/automatic?
--
--
-- If we can index the structure, i.e. find a type i such that each
-- substructure has a corresponding i, then we can memoize i -> s in order to
-- share intermediate computations.  In the above case, the index is (Int,Int).
-- 
-- There is an analogy with computable reals somewhere here:

{- 
        |----------------------------------------|
        |--------------A----------------|
        |----------AA----------|            
                  |---------AB----------|
                  |----------------B-------------| 
                  |---------BA----------|
                               |--------BB-------|
-}

data Interval a = a :.. a
    deriving (Show)

a,b,c :: Interval Rational
a = 0 :.. (1/2)
b = (1/4) :.. (3/4)
c = (1/2) :.. 1


instance (Ord a, Num a) => Num (Interval a) where
    (x :.. x') + (y :.. y') = (x + y) :.. (x' + y')
    negate (x :.. x')   = negate x' :.. negate x
    (x :.. x') * (y :.. y') = minimum subs :.. maximum subs
        where
        subs = [x*y,x*y',x'*y,x'*y']
    abs (x :.. y)
        | x <= 0 && y <= 0 = negate (x :.. y)
        | x <= 0 && y >= 0 = 0 :.. max (negate x) y
        | x >= 0 && y >= 0 = x :.. y
    signum (x :.. y)
        | x <= 0 && y <= 0 = -1
        | x <= 0 && y >= 0 = (-1) :.. 1
        | x >= 0 && y >= 0 = 1
    fromInteger x = fromInteger x :.. fromInteger x

(|*|) :: (Num a) => Interval a -> Interval a -> Interval a
(x :.. x') |*| (y :.. y') = (x+y*d) :.. (x+y'*d)
    where
    d = x' - x
