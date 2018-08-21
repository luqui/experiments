{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}

import Prelude hiding (id, (.))
import Control.Category
import Data.Kind (Constraint, Type)

newtype R a = R a

data Iso a b = Iso { to :: a -> b, from :: b -> a }

instance Category Iso where
    id = Iso id id
    Iso f f' . Iso g g' = Iso (f . g) (g' . f')

inverse :: Iso a b -> Iso b a
inverse (Iso f f') = Iso f' f

class IsoFunctor f where
    isomap :: Iso a b -> f a -> f b

liftIso :: (IsoFunctor f) => Iso a b -> Iso (f a) (f b)
liftIso i = Iso (isomap i) (isomap (inverse i))


data Rep f a where
    Rep :: Iso b a -> f b -> Rep f a

instance IsoFunctor (Rep f) where
    isomap i (Rep m f) = Rep (i . m) f

use :: (IsoFunctor g) => (forall x. f x -> g x) -> Rep f a -> g a
use c (Rep m f) = isomap m (c f)

cons :: f a -> Rep f a
cons = Rep id

{-
(use id . cons) f
  == use id (cons f)
  == use id (Rep id f)
  == isomap id (id f)
  == isomap id f
  == f
QED


(cons . use id) (Rep m f)
  == cons (use id (Rep m f))
  == cons (isomap m (id f))
  == cons (isomap m f)
  == Rep id (isomap m f)

The (iso)free theorem says

  f :: Iso A B
  ------------
  isomap f . p_A = p_B . isomap f

So

  Rep id (isomap m f)
  == (Rep id . isomap m) f
  == (isomap m . Rep id) f
  == isomap m (Rep id f)
  == Rep (m . id) f 
  == Rep m f
QED
-}
