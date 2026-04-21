module Main where

import Prelude
import Effect.Console (log)

x :: forall a. a -> String
x a = y "Test"
  where
  y :: forall a. Show a => a -> String
  y a = ?test (a :: a)

main = do
  log (x 0)
  log "Done"
