{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GADTs, DataKinds, PolyKinds, LambdaCase, TypeOperators, EmptyCase, BangPatterns, RankNTypes #-}

-- The Weak König Lemma says that every infinite binary tree has an infinite
-- path.  WKL is a non-computable axiom -- in that from a computable infinite
-- path it is not possible to compute an infinite path.  However, if we allow
-- continuations as a computational effect, then WKL is computable.  That is,
-- we can compute an infinite path, as long as we are allowed to change our
-- mind about earlier decisions.

import Control.Monad.Trans.Cont
import Control.Monad.IO.Class
import Data.Type.Equality

data Finity = Finite | Infinite

type ClassicalJoinInf t t' t'' = forall v. (t'' :~: 'Infinite) -> (t :~: 'Infinite -> v) -> (t' :~: 'Infinite -> v) -> v

data Tree t a where
    Leaf :: Tree 'Finite a
    Branch :: ClassicalJoinInf t t' t'' -> a -> Tree t a -> Tree t' a -> Tree t'' a

instance Functor (Tree t) where
    fmap _ Leaf = Leaf
    fmap f (Branch j x l r) = Branch j (f x) (fmap f l) (fmap f r)

data ContStream v m a = Cons a (ContT v m (ContStream v m a))

exmid :: ContT v m (Either a (a -> m v))
exmid = ContT (\c -> c (Right (\x -> c (Left x))))

classical :: ((a -> m v) -> m v) -> ContT v m a
classical = ContT

wklC :: t :~: 'Infinite -> Tree t a -> ContT v m (ContStream v m a)
wklC tinf Leaf = case tinf of {}
wklC tinf (Branch joininf x l r) = do
    pure . Cons x $ exmid >>= \case
        Left linf -> wklC linf l
        Right notlinf -> do
            rinf <- classical (joininf tinf notlinf)
            wklC rinf r

leftTree :: Int -> Tree 'Infinite Int
leftTree !n = Branch (\_ p _ -> p Refl) n (leftTree (n+1)) Leaf

showStream :: (Show a) => ContStream v IO a -> ContT v IO ()
showStream (Cons x xs) = do
    liftIO $ print x
    showStream =<< xs

bigFiniteTree :: Int -> Tree 'Finite Int
bigFiniteTree 0 = Leaf
bigFiniteTree n = Branch (\p _ _ -> case p of {}) n (bigFiniteTree (n-1)) (bigFiniteTree (n-1))

-- This always picks the infinite branch.  The magic is actually in ClassicalJoinInf, which secretly tells 
-- us which branch to take.  It is not so classical, after all.  I have proved nothing.
exampleTree :: Tree 'Infinite String
exampleTree = Branch (\Refl p _ -> p Refl) "root" (("infinite " ++) . show <$> leftTree 0) (("finite " ++) . show <$> bigFiniteTree 10)

main :: IO ()
main = (`runContT` (const (pure ()))) $ do
    path <- wklC Refl exampleTree
    showStream path
