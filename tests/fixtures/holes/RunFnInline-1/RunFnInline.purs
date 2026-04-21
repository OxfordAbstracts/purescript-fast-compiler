module Main where

import Prelude

import Effect.Console (log)

runFn3 :: forall a b c d. (a -> b -> c -> d) -> a -> b -> c -> d
runFn3 f a b c = ?test

main = do
  log $ runFn3 (\a b c -> c) 1 2 "Done"
