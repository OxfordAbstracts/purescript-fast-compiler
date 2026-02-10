module Effect.Shuffle
  ( pick
  , pickMonoid
  , pickNonEmpty
  , pickOr
  , shuffle
  ) where

import Prelude

import Data.Array (fromFoldable, index, range, reverse, toUnfoldable, updateAt)
import Data.Array.NonEmpty (NonEmptyArray, head, toArray)
import Data.Foldable (class Foldable, foldM, indexl, length)
import Data.Maybe (Maybe, fromMaybe)
import Data.Unfoldable (class Unfoldable)
import Effect (Effect)
import Effect.Random (randomInt)

shuffle_ ∷ ∀ a. Array a → Effect (Array a)
shuffle_ arr = foldM step arr ns
  where
  n = length arr

  ns = reverse $
    if n <= 1 then [] else range 1 (n - 1)

  step acc i = do
    j ← randomInt 0 i
    pure $ fromMaybe acc do
      x ← index acc i
      y ← index acc j
      updateAt i y =<< updateAt j x acc

shuffle ∷ ∀ f a. Foldable f ⇒ Unfoldable f ⇒ f a → Effect (f a)
shuffle = map toUnfoldable <<< shuffle_ <<< fromFoldable

pick ∷ ∀ f a. Foldable f ⇒ Unfoldable f ⇒ f a → Effect (Maybe a)
pick = map (indexl 0) <<< shuffle

pickOr ∷ ∀ f a. Foldable f ⇒ Unfoldable f ⇒ a → f a → Effect a
pickOr fallback arr = fromMaybe fallback <$> pick arr

pickMonoid ∷ ∀ f a. Foldable f ⇒ Unfoldable f ⇒ Monoid a ⇒ f a → Effect a
pickMonoid = pickOr mempty

pickNonEmpty ∷ ∀ a. NonEmptyArray a → Effect a
pickNonEmpty arr = pickOr (head arr) $ toArray arr
