module Main where

import Prelude
import Effect.Console (log)

foo :: forall a. {b :: Number | a} -> {b :: Number | _}
foo f = ?test

main = log "Done"
