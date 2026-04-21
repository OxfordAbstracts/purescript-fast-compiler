module Main where

import Prelude
import Effect.Console

shout = log <<< (_ <> "!") <<< show

-- Here, we should simplify the context so that only one Show
-- constraint is added.
usesShowTwice true = ?test
usesShowTwice false = logShow

main = do
  usesShowTwice true "Test"
  log "Done"
