module Main where

import Effect.Console (log)
import Lib

main = do
  let q = ?test (4 /\ 4)
  log "Done"
