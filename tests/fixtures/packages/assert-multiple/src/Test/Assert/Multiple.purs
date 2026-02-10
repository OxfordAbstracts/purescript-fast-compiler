module Test.Assert.Multiple where

import Prelude
import Data.Foldable (class Foldable, foldl)
import Effect (Effect)

resolve :: ∀ m. Monad m => Foldable m => m (Effect Unit) -> Effect Unit
resolve arr = foldl res mempty arr
  where
  res acc x = do
    _ <- acc
    x
