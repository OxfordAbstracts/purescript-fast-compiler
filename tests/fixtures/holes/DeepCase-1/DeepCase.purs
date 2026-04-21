module Main where

import Prelude
import Effect.Console (log, logShow)

f x y =
  ?test

main = do
  logShow $ f 1.0 10.0
  log "Done"
