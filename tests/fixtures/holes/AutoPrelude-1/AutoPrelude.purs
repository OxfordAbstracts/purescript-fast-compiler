module Main where

import Prelude
import Effect.Console (log)

f x = x * 10.0
g y = ?test

main = do
  log $ show $ (f <<< g) 100.0
  log "Done"
