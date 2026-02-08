module Test.Util where

import Prelude

import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (modify_, new, read)

memoizeEffect :: forall a b. Ord a => (a -> Effect b) -> Effect (a -> Effect b)
memoizeEffect f = do
  cacheRef <- new Map.empty
  pure \x -> do
    cache <- read cacheRef
    case Map.lookup x cache of
      Just result -> pure result
      Nothing -> do
        result <- f x
        modify_ (Map.insert x result) cacheRef
        pure result