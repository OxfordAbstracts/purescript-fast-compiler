module Main where

import Effect.Console (log)

f = \(x :: forall a. a -> a) -> x x

test1 = (f \x -> x) 1

g = \(x :: (forall a. a -> a) -> Int) -> x (\y -> y)

test2 = ?test

main = log "Done"
