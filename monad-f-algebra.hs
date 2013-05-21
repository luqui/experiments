{-# LANGUAGE RankNTypes, TypeOperators, GADTs, KindSignatures, TypeSynonymInstances, FlexibleInstances #-}

-- Functor is the class of endofunctors over Hask.

-- A natural transformation between Functors.
newtype f ~> g = NT { (%) :: forall a. f a -> g a }

-- Composition of natural transformations.
(.*) :: (g ~> h) -> (f ~> g) -> (f ~> h)
g .* f = NT $ \x -> g % (f % x)

-- NFunctor is the class of endofunctors over the category
-- of Functors (endofunctors over Hask) & natural transformations.
class NFunctor f where
    nfmap :: (a ~> b) -> (f a ~> f b)

data MonadF :: (* -> *) -> (* -> *) where
    Return :: a -> MonadF m a
    Bind   :: (a -> m b) -> m a -> MonadF m b

-- MonadF is such a functor.
instance NFunctor MonadF where
    nfmap = \f -> NT (go f)
        where
        go f (Return a) = Return a
        go f (Bind t m) = Bind ((f %) . t) (f % m)


-- F-Algebras over NFunctors
type NAlgebra f a = f a ~> a

-- Every monad gives rise to a MonadF-Algebra
monadNAlgebra :: (Monad m) => NAlgebra MonadF m
monadNAlgebra = NT go
    where
    go (Return a) = return a
    go (Bind f x) = f =<< x


-- Every MonadF-Algebra gives rise to a monad.  
-- (It will not necessarily satisfy the laws, there are constraints
-- on the f-algebra)
algReturn :: NAlgebra MonadF m -> a -> m a
algReturn alg x = alg % Return x

algBind :: NAlgebra MonadF m -> (a -> m b) -> m a -> m b
algBind alg f m = alg % Bind f m


-- The category of functors has products
data (f * g) a = Prod (f a) (g a)

fstF :: f * g ~> f
fstF = NT $ \(Prod a _) -> a

sndF :: f * g ~> g
sndF = NT $ \(Prod _ b) -> b

(***) :: (f ~> g) -> (f ~> h) -> (f ~> (g * h))
f *** g = NT $ \x -> Prod (f % x) (g % x)



-- And we can take products of F-Algebras

nproduct :: (NFunctor f) => NAlgebra f a -> NAlgebra f b -> NAlgebra f (a * b)
nproduct f g = (f .* nfmap fstF) *** (g .* nfmap sndF)


-- Which means we can take products of monads.  E.g. here's 
-- Maybe * IO

type MaybeIO = Maybe * IO

readerIOAlg :: NAlgebra MonadF MaybeIO
readerIOAlg = nproduct monadNAlgebra monadNAlgebra

instance Monad MaybeIO where
    return = algReturn readerIOAlg
    (>>=)  = flip (algBind readerIOAlg)

-- It's really about two monadic computations sharing some structure.
-- For example:
thingy :: MaybeIO [Int]
thingy = do 
    x <- Prod (Just 10) readLn
    mapM (\a -> Prod (Just a) readLn) [1..x]

-- Unclear if it's useful to take products of monads...

runThingy :: IO ()
runThingy = do
    let Prod m io = thingy
    putStrLn "Maybe:"
    print m
    putStrLn "IO:"
    print =<< io
    
