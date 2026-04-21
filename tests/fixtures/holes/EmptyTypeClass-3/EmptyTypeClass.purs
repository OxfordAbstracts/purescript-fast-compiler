module Main where

import Prelude
import Effect
import Effect.Console

head :: forall a. Partial => Array ?test -> a
head [x] = x

main :: Effect _
main = log "Done"
