module Main where

import Effect.Console (log)

test :: forall a. ?test -> a
test = \(x :: a) -> x

main = log "Done"
