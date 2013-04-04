-- I think it should be possible to take the derivative (find the type 
-- of one-hole contexts) of an arbitrary Traversable.  

{-
data X a = X a a a

-- becomes

data DX a b = X1 b a a | X2 a b a | X3 a a b

-- so for each occurrence of a, we get a case of the derivative.

traverse f (X a b c) = X <$> f a <*> f b <*> f c

-- So we need some applicative functor F and some function f
-- such that each time f is applied, we get a new sum case with
-- the other values held fixed. 

X <$> [open, a] <*> [open, b] <*> [open, c]

-- Except it is not applied like a cartesian product, because only
-- one open can happen at a time.  Also we need some way to represent
-- which case we are in.

-- I think we want to return a list of zippers, actually.

[ X1 (f a) b c, X2 a (f b) c, X3 a a (f c) ]

-- Or probably even an X of zippers.

X (X1 (f a) b c) (X2 a (f b) c) (X3 a b (f c))

-- So each a gets replaced by a the whole data structure where that position
-- is a hole, and the rest of the data structure is held fixed.  (This is feeling
-- very comonadic, but I'm going to stick to the Traversable course)

-- The context

X1 _ b c

-- is basically a way to construct an X once you've filled in the hole

(a -> X a)

-- So the question is, can we express the appropriate function of type 

X a -> X (a -> X a)

-- as a traversal?  

-- We can map the structure without mapping the hole

X1 _ b c --> X1 _ (f b) (f c)

-- (but changing the type of the hole)

-- That is, we have 

fmap :: (a -> b) -> (a -> X a) -> (b -> X b)

-- So clearly these are not arbitrary functions, there needs to be some extra structure.

X (Maybe a)

-- would do it, at the cost of a lot of junk.  What about

b |-> X (Either a b)

-- which is linear in b?  I've already discovered

-}

{-# LANGUAGE TypeOperators, TupleSections, ExistentialQuantification, RankNTypes #-}

import Control.Applicative
import Data.Traversable
import Control.Arrow

class (Functor t) => Linear t where
    lsequence :: (Functor f) => t (f a) -> f (t a)

instance Linear ((,) w) where
    lsequence (x,f) = (x,) <$> f

-- So if X ∘ Either a is linear, then it is a one-hole context for X a

infixr 9 ∘
newtype (g ∘ f) a = O { getO :: g (f a) }

instance (Functor g, Functor f) => Functor (g ∘ f) where
    fmap f (O x) = O $ (fmap.fmap) f x

instance (Linear g, Linear f) => Linear (g ∘ f) where
    lsequence (O f) = fmap O . lsequence . fmap lsequence $ f

-- data D t a b = Linear (t ∘ Either a) => D ((t ∘ Either a) b)

-- But that's cumbersome.  There's a better way, just make the lsequence dictionary explicit:

type (+) = Either

data D t a b = D { 
    lseqL :: forall f x. Functor f => t (a + f x) -> f (t (a + x)),
    cx    :: t (a + b)
}

-- Although this has the required property of being a functor

instance Functor t => Functor (D t a) where
    fmap f d = D { lseqL = lseqL d, cx = (fmap.fmap) f (cx d) }

-- it fails at also being covariant in a.

-- We can correct it by transforming a into an index set

data D_1 t a b = forall ix. D_1 {
    lseqL_1 :: forall f x. Functor f => t (ix + f x) -> f (t (ix + x)),
    cx_1    :: t (ix + b),
    index_1 :: ix -> a
}

-- Which is ugly as fuck, but it's covariant in both of its arguments.  I
-- guess it makes sure that lseqL_1 can't change any a's along the way.

-- Unfortunately, I don't think it captures what we are looking for.  We want
-- the subset of functors t' of t such that t' (a + b) is linear in b; not that
-- t (a + b) is linear in b for all of its values.  (I'm kinda glad, because I
-- don't want the solution to be that ugly ass-thing).

-- That is, 
-- D t a (b + c) = D t a b + D t a c.   -- it's linear in the hole
-- D t a a       = t a                  -- it's a one hole context
--
-- So,
-- D t a (f a)  -> f (D t a a)            -- linearity
--              =  f (t a)   

