module Main where

import Prelude
import Effect.Console

greet { greeting, name } = ?test

main = do
  greet { greeting: "Hello", name: "World" }
  log "Done"
