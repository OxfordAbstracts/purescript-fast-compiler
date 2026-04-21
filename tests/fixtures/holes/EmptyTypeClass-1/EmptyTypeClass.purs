module Main where

import Prelude
import Effect
import Effect.Console

head :: forall a. Partial => Array a -> a
head [x] = ?test

main :: Effect _
main = log "Done"
