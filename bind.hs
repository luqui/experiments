{-# LANGUAGE RankNTypes #-}

type Thunk a = () -> a
type Ch a = forall r. (a -> Thunk r -> r) -> Thunk r -> r

pure :: a -> Ch a
pure x result fail = result x fail

bind :: (a -> Ch b) -> Ch a -> Ch b
bind f a result fail = a (\x xs -> f x result xs) fail

toList :: Ch a -> [a]
toList a = a (\x xs -> x : xs ()) (\() -> [])
