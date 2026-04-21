module Main where

import Prelude
import Prim.TypeError (class Warn, Text)
import Effect.Console (log)

foo :: forall t. Warn (Text "Example") => t -> ?test
foo x = x

main = when (foo 42 == 42) $ log "Done"
