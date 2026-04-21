module Main where

import Prelude
import Effect.Console (log)

data Foo r = Foo { | r }

test :: ?test ()
test = Foo {}

main = log "Done"
