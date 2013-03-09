{-# LANGUAGE RankNTypes #-}

newtype Nondet a = Nondet { runNondet :: forall r. (a -> r -> r) -> r -> r }

instance Functor Nondet where
    fmap f a = Nondet $ \result fail -> runNondet a (\x xs -> result (f x) xs) fail

toList :: Nondet a -> [a]
toList a = runNondet a (:) []

fromList :: [a] -> Nondet a
fromList [] = Nondet $ \result fail -> fail
fromList (x:xs) = Nondet $ \result fail -> result x (runNondet (fromList xs) result fail)

pair :: Nondet a -> Nondet b -> Nondet (a,b)
pair a b = Nondet $ \result fail ->
    runNondet a (\x xs ->
        runNondet b (\y ys ->
            result (x,y) ys)
        xs)
    fail
