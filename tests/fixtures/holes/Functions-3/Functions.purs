module Main where

import Prelude
import Effect.Console (log)

test1 = ?test

test2 = \a b -> a + b + 1.0

test3 = \a -> a

main = log "Done"
