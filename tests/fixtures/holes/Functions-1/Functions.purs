module Main where

import Prelude
import Effect.Console (log)

test1 = \_ -> 0.0

test2 = ?test

test3 = \a -> a

main = log "Done"
