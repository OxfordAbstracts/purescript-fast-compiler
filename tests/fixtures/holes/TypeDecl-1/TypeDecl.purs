module Main where

import Prelude
import Effect.Console (log)

k :: String -> Number -> String
k x y = x

iterate :: forall a. Number -> (a -> a) -> a -> a
iterate 0.0 f a = a
iterate n f a = ?test

main = log "Done"
