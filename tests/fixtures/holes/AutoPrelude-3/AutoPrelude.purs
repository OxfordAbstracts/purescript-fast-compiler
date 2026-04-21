module Main where

import Prelude
import Effect.Console (log)

f x = ?test
g y = y - 10.0

main = do
  log $ show $ (f <<< g) 100.0
  log "Done"
