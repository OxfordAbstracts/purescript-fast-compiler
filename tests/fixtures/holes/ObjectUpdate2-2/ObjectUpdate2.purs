module Main where

import Prelude
import Effect.Console (log)

type X r = { | r }

x :: X (baz :: String)
x = { baz: "baz" }

blah :: forall r. X r -> X r
blah x = x

test = ?test x
  { baz = "blah"
  }

main = log "Done"
