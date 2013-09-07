module PreludePlus 
    ( module Prelude
    , module Data.Foldable
    , module Data.Traversable
    , module Control.Applicative
    , module Control.Arrow
    , module Control.Monad
    , module Data.Monoid
    )
where

import Prelude hiding
    ( mapM_, sequence_, foldl1, maximum, minimum, product, sum, foldr, all
    , and, any, concatMap, elem, foldl, foldr1, notElem, or, concat
    , mapM, sequence
    )
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Arrow ((***), (&&&), (+++), (|||), left, right, first, second)
import Control.Monad (join, (<=<), (>=>), MonadPlus(..), guard, when)
import Data.Monoid hiding (mconcat)  -- `fold` is more general
