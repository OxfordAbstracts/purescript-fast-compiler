module Main where

import Prelude
import Effect.Console (log)

foo = bar
  where bar r = r + 1.0

r = ?test

main = log "Done"
