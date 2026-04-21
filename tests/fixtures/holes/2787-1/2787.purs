module Main where

import Prelude
import Effect.Console

main
  | between 0 1 2 = ?test "Fail"
  | otherwise = log "Done"
