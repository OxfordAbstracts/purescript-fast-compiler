module Classes.HasUuid where

import Prelude
import Data.Array (filter)

class HasUuid m where
  getUuid :: m -> Int
  setUuid :: Int -> m -> m

matchObjectsOnId :: forall a b. HasUuid a => HasUuid b => a -> b -> Boolean
matchObjectsOnId obj obj' = getUuid obj == getUuid obj'

notMatchObjectsOnId :: forall a b. HasUuid a => HasUuid b => a -> b -> Boolean
notMatchObjectsOnId = not <<< matchObjectsOnId

infix 4 matchObjectsOnId as ===

infix 4 notMatchObjectsOnId as !==

replaceInArray
  :: forall a f
   . HasUuid a
  => Functor f
  => a
  -> f a
  -> f a
replaceInArray replacement objs = (\obj -> if replacement === obj then replacement else obj) <$> objs

compareUuid :: forall a b. HasUuid a => HasUuid b => a -> b -> Ordering
compareUuid a b = compare (getUuid a) (getUuid b)

removeFromArray
  :: forall a
   . HasUuid a
  => a
  -> Array a
  -> Array a
removeFromArray x xs = filter (not <<< (===) x) xs