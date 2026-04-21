module Main where

import Effect.Console
import A

bar :: ?test
bar = true

main = do
  logShow (show bar)
  log "Done"
