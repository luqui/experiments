I want kinds to be categories.  It is not necessarily true that types
(objects of kinds) need to have values.  In fact, I suppose it is quite
like the Agda formulation, maybe with some nicer syntax and a looser
approach.  It ought to be possible to transport objects that are in more
than one category at a time by isomorphism.

There are kind-polymorphic constructions, such as

    (->) :: k * k -> Set
    (*)  :: k * k -> k

which can take on different meaning depending on what kind you are
talking about.  However, they come with operations, e.g.

    (.) :: (b -> c) * (a -> b) -> (a -> c)

is always available whenever (->) is, and

    (&&&) :: (a -> b) * (a -> c) -> (a -> b * c)
    fst :: a * b -> a
    snd :: a * b -> b

are always available whenever (*) is.

This leads us to either a subkinding system or a kind-class system. E.g.

    fst :: forall (k <= Products) (a b :: k). a * b -> a

or

    fst :: forall k (a b :: k). Products k => a * b -> a

Of course, the kind-class system would have all the limitations of
Haskell's type-class system; nature of the beast.

But I'm also interested in allowing multiple implementations of 
Products k, and *since* they are all isomorphic they can be omitted.
E.g. with a Products kind-class

    Products k = class where
        (*) :: k -> k -> k
        (&&&) :: (a -> b) * (a -> c) -> (a -> b * c)
        fst :: a * b -> a
        snd :: a * b -> b

you might implement it 

    PairProducts = instance Products Set where
        (*) = (,)
        (f &&& g) x = (f x, g x)
        fst (x,y) = x
        snd (x,y) = y

(assuming there is a definite Set in which to work; I'd maybe like to
stay more abstract than that -- no wait, it seems that a philosophy here
is to stay concrete and allow transportation.  But I digress)

And you would have to call

    fst[PairProducts] (1,2)

(Although maybe you could deduce that that was the instance you wanted
from the type (,); i.e. we have some sort of layered kind/type class
system)

*However*, I could imagine special support for isomorphism that would
allow you to omit it, with the knowledge that it doesn't matter which
one you use

    prodIso :: (Products k)[p], (Products k)[p']
            => (a *[p] b) -> (a *[p'] b)
    prodIso = fst[p] &&&[p'] snd[p]

    declare isomorphism Products k = prodIso

And maybe you could then also declare defaults for some kinds.

As for multi-layered classes, I think that's just MPTCs

    class Products k ((*) :: k -> k -> k) where
        ...

    PairProducts = instance Products Set (,) where
        ...

And then our isomorphism is

    prodIso :: Products k p -> Products k p'

(oh! of course, we can have morphisms in Constraint!)

(Hmm but is that what we want?  All we really need is a morphism from a
*[p] b to a *[p'] b -- are we trying to declare a morphism in a category
of product constructions over a category?  What would that be?

Objects:   functors : C x C -> C & operations (i.e. Products instances)
Morphisms: for p -> p', (*[p]) -> (*[p']) nat. trans.

So that means that Products k is also a kind!  And then we would prove
that it is a trivial kind:

    trivial :: a -> b | Products k  -- | specifies kind?
    trivial = fst &&& snd           -- is this inferrable to this degree?

    trivial[p -> p'] = fst[p] &&&[p'] snd[p]

And so in order to omit a constraint where it appears, you need to
instantiate

    Omit = class (c :: k -> Constraint) where
        trivial :: a -> b | c

(Assuming there is a uniform way to make class categories.)
