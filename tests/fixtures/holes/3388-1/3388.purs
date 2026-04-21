module Main where

import Prelude
import Effect.Console (log)

main = do
  let
    x = ?test
    { a, b } = x { a = 43 }
  log "Done"
