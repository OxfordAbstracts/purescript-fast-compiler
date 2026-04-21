module Main where

import Effect.Console (log)

test :: forall a. a -> ?test
test = \(x :: a) -> x

main = log "Done"
