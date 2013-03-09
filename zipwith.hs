{-# LANGUAGE RankNTypes  #-}

import Prelude hiding (zipWith)

newtype ChList a = ChList { fold :: forall b. (a -> b -> b) -> b -> b }

nil :: ChList a
nil = ChList $ \f z -> z

cons :: a -> ChList a -> ChList a
cons x xs = ChList $ \f z -> f x (fold xs f z)

uncons :: ChList a -> Maybe (a, ChList a)
uncons xs = fold xs (\x -> Just . (,) x . maybe nil (uncurry cons)) Nothing

zipWith :: (a -> b -> c) -> ChList a -> ChList b -> ChList c
zipWith f xs ys = ChList $ \g z -> 
        fold xs (\x xsf ys -> 
             maybe z (\(y,ys) -> g (f x y) (xsf ys)) (uncons ys)
        ) (const z) ys

toList :: ChList a -> [a]
toList xs = fold xs (:) []

fromList :: [a] -> ChList a
fromList xs = ChList $ \f z -> foldr f z xs
