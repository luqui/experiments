> {-# LANGUAGE DeriveFunctor
>            , DeriveFoldable
>            , DeriveTraversable
>            , TypeOperators #-}
>
> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

Certain kinds of typeclasses have some very regular instances.  For example, it
is obvious how to implement `(Num a, Num b) => Num (a,b)` and `(Monoid a, Monoid
b) => Monoid (a,b)`, and similarly if `F` is some applicative functor, `(Num a)
=> Num (F a)` and `(Monoid a) => (Monoid F a)` are obvious.  Furthermore, these
instances (and many others) seem to be obvious in the same way.  

    (+) a b     = (+)     <$> a <*> b
    mappend a b = mappend <$> a <*> b

    fromInteger n = pure (fromInteger n)
    mempty        = pure mempty

And take them on pairs:

    (x,x')     +     (y,y')  = (x     +     y, x'     +     y')
    (x,x') `mappend` (y,y')  = (x `mappend` y, x' `mappend` y')

    fromInteger n = (fromInteger n, fromInteger n)
    mempty        = (mempty       , mempty)

It would be straightforward for these cases to derive the necessary
implementations from the type signature.  However, it would be nice if there
were a more abstract perspective, such that we didn't have to inspect the type
signature to find the operations -- that they could arise from some other
standard construction.  Further, it is not quite as obvious from the the type
signature how to automatically instantiate methods such as

    mconcat :: (Monoid m) => [m] -> m

without making a special case for `[]`, whereas hopefully a more abstract
perspective would inform us what kinds of type constructors would be supported.

In this post, we will see such an abstract perspective.  It comes from
(surprise!) category theory.  I disclaim that I'm still a novice with category
theory (but in the past few weeks I have gained competence by studying).  So we
will not get very deep into the theory, just enough to steal the useful concept
and leave the rest behind.  I welcome relevant insights from the more
categorically educated in the comments.

F-Algebras
----------

The unifying concept we will steal is the
[*F-algebra*](http://en.wikipedia.org/wiki/F-algebra).  An F-algebra is a
Functor `f` and a type `a` together with a function `f a -> a`.  We can make
this precise in Haskell:

> type Algebra f a = f a -> a

I claim that `Num` and `Monoid` instances are F-algebras over suitable functors.
Look at the methods of `Monoid`:

    mempty :: m
    mappend :: m -> m -> m

We need to find a functor `f` such that we can recover these two methods from a
function of type `f m -> m`.  With some squinting, we arrive at:

> data MonoidF m
>     = MEmpty
>     | MAppend m m
>
> memptyF :: Algebra MonoidF m -> m
> memptyF alg = alg MEmpty 
>
> mappendF :: Algebra MonoidF m -> (m -> m -> m)
> mappendF alg x y = alg (MAppend x y)

**Exercise 1:** work out the functor `NumF` over which
[`Num`](http://www.haskell.org/ghc/docs/latest/html/libraries/base/Prelude.html3t:Num)
instances are F-algebras, and write the methods of `Num` in terms of it.

**Exercise 2:** for each of the standard classes 
[`Eq`](http://www.haskell.org/ghc/docs/latest/html/libraries/base/Prelude.html#t:Eq), 
[`Read`](http://www.haskell.org/ghc/docs/latest/html/libraries/base/Prelude.html#t:Read), 
[`Show`](http://www.haskell.org/ghc/docs/latest/html/libraries/base/Prelude.html#t:Show), 
[`Bounded`](http://www.haskell.org/ghc/docs/latest/html/libraries/base/Prelude.html#t:Bounded),
and [`Integral`](http://www.haskell.org/ghc/docs/latest/html/libraries/base/Prelude.html#t:Integral),work out whether they are expressible as F-algebras.  If so, give the functor; if not, explain or 
prove why not.

**Exercise 3:** write a function `toMonoidAlg` which finds the `MonoidF`-algebra
for a given instance `m` of the `Monoid` class.

Combining Instances
-------------------

Motivated by the examples in the introduction, we can find the "instance" for
pairs given instances for each of the components.

> pairAlg :: (Functor t) => Algebra t a -> Algebra t b -> Algebra t (a,b)
> pairAlg alga algb tab = (alga (fmap fst tab), algb (fmap snd tab))

Also, we hope we can find the instance for an applicative functor given an
instance for its argument

    applicativeAlg :: (Functor t, Applicative f) 
                   => Algebra t a -> Algebra t (f a)

but there turns out to be trouble:

    applicativeAlg alg tfa = ...

We need to get our hands on an `t a` somehow, and all we have is a `t (f a)`. 
This hints at something from the standard library:

    sequenceA :: (Traversible t, Applicative f) => t (f a) -> f (t a)

which indicates that our functor needs more structure to implement
`applicativeAlg`.

> applicativeAlg :: (Traversable t, Applicative f) 
>                => Algebra t a -> Algebra t (f a)
> applicativeAlg alg tfa = fmap alg (sequenceA tfa)

Now we should be able to answer the query from the beginning:

**Exercise 4:** For what kinds of type constructors `c` is it possible to
automatically derive instances for *(a)* pairs and *(b)* `Applicative`s for a
typeclass with a method of type `c a -> a`.  (e.g. `mconcat :: [a] -> a`).
Demonstrate this with an implementation.

Combining Classes
-----------------

Intuitively, joining the methods of two classes which are both expressible as
F-algebras should give us another class expressible as an F-algebra.  This is
demonstrated by the following construction:

> data (f :+: g) a = InL (f a) | InR (g a)
>     deriving (Functor, Foldable, Traversable)
>
> coproductAlg :: (Functor f, Functor g) 
>              => Algebra f a -> Algebra g a -> Algebra (f :+: g) a
> coproductAlg falg _ (InL fa) = falg fa
> coproductAlg _ galg (InR ga) = galg ga

So now we can model a subclass of both `Num` and `Monoid` by `type NumMonoidF =
NumF :+: MonoidF`.

**Exercise 5:** We hope to be able to recover `Algebra NumF a` from `Algebra
NumMonoidF a`, demonstrating that the latter is in fact a subclass.  Implement
the necessary function(s).

**Exercise 6:** Given the functor product definition

> data (f :*: g) a = Pair (f a) (g a)
>     deriving (Functor, Foldable, Traversable)

find a suitable combinator for forming algebras over a product functor. It may
not have the same form as coproduct's combinator!  What would a typeclass formed
by a product of two typeclasses interpreted as F-algebras look like?

Free Constructions
------------------

One of the neat things we can do with typeclasses expressed as F-algebras is
form free monads over them -- i.e. form the data type of a "syntax tree" over
the methods of a class (with a given set of free variables).  Begin with the
free monad over a functor:

> data Free f a
>     = Pure a
>     | Effect (f (Free f a))
>     deriving (Functor, Foldable, Traversable)
>
> instance (Functor f) => Monad (Free f) where
>     return = Pure
>     Pure a >>= t = t a
>     Effect f >>= t = Effect (fmap (>>= t) f)

([Church-encoding](http://hackage.haskell.org/package/free-functors-0.1.1) this
gives better performance, but I'm using this version for expository purposes)

`Free f a` can be interpreted as a syntax tree over the typeclass formed by `f`
with free variables in `a`.  This is also called an "initial algebra", a term
you may have heard thrown around in the Haskell community from time to time.  We
demonstrate that a free construction over a functor is a valid F-algebra for
that functor:

> initialAlgebra :: (Functor f) => Algebra f (Free f a)
> initialAlgebra = Effect

And that it is possible to "interpret" an initial algebra using any other
F-algebra over that functor.  

> initiality :: (Functor f) => Algebra f a -> Free f a -> a
> initiality alg (Pure a) = a
> initiality alg (Effect f) = alg (fmap (initiality alg) f)

**Exercise 7:** Give a monoid isomorphism (a bijection that preserves the
monoid operations) between `Free MonoidF` and lists `[]`, ignoring that Haskell
allows infinitely large terms.  Then, using an infinite term, show how this
isomorphism fails. 

*Next time: F-Coalgebras*
