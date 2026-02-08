module Data.Semigroup.Foldable.Extra where

import Control.Bind (discard, pure)
import Control.Monad.State (put, runState)
import Data.Maybe (Maybe(..))
import Data.Semigroup.Traversable (class Traversable1, traverse1)
import Data.Tuple (Tuple(..))

-- | Map an array conditionally, only return the array when at least one element was mapped.
-- | Elements that are not mapped will keep the old value.
-- |
-- | Hint: mapAll can be found in Data.Semigroup.Traversable.Extra
-- |
-- | ```purescript
-- | mapAny (\_ -> Nothing) (Data.Array.NonEmpty.cons' 1 [2, 3]) == Nothing
-- | mapAny (\x -> if x == 2 then Just 99 else Nothing) (Data.Array.NonEmpty.cons' 1 [2, 3]) == Data.Array.NonEmpty.fromArray [1,99,3]
-- | ```
-- | Not that in the second example the `Just` is implicit.
mapAny :: forall a f. Traversable1 f => (a -> Maybe a) -> f a -> Maybe (f a)
mapAny f xs =
  let go x = case f x of
        Nothing -> pure x
        Just y -> do
          put true
          pure y

      Tuple acc replaced = runState (traverse1 go xs) false

  in  if replaced then
        Just acc
      else
        Nothing
