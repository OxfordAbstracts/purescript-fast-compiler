module Main where

import Prelude
import Effect.Console

main
  | ?test 0 1 2 = log "Fail"
  | otherwise = log "Done"
