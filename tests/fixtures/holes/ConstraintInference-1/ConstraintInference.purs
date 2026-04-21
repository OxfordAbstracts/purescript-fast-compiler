module Main where

import Prelude
import Effect.Console (log)

shout = ?test

main = do
  shout "Test"
  log "Done"
