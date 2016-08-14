{-# LANGUAGE LambdaCase #-}

import Prelude hiding (null)
import qualified Data.Searchable as S
import Data.Function (fix)


data Set
    = Empty
    | Nonempty (S.Set Set)

member :: Set -> Set -> Bool
x `member` Empty = False
x `member` Nonempty a = x `S.member` a

forevery :: Set -> (Set -> Bool) -> Bool
forevery Empty _ = True
forevery (Nonempty a) p = S.forevery a p

subset :: Set -> Set -> Bool
subset a b = forevery a (`member` b)

instance Eq Set where
    a == b = (a `subset` b) && (b `subset` a)

null :: Set -> Bool
null Empty = True
null _ = False

singleton :: Set -> Set
singleton = Nonempty . S.singleton

union :: Set -> Set -> Set
union Empty b = b
union a Empty = a
union (Nonempty a) (Nonempty b) = Nonempty (a `S.union` b)

bigUnion :: Set -> Set
bigUnion Empty = Empty
bigUnion (Nonempty a) =
    case S.search a (not . null) of
        Just Empty -> error "impossible: Just Empty"
        Just (Nonempty v) -> Nonempty (S.bigUnion (fmap (\case Empty -> v; Nonempty s -> s) a))
        Nothing -> Empty

transitive :: Set -> Bool
transitive a = forevery a (`subset` a)

ordinal :: Set -> Bool
ordinal a = transitive a && forevery a transitive



zeroO :: Set
zeroO = Empty

succO :: Set -> Set
succO x = x `union` singleton x

toO :: Integer -> Set
toO 0 = zeroO
toO n = succO (toO (n-1))


