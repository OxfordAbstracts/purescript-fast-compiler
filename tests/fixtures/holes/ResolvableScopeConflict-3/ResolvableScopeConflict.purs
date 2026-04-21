module Main where

import A (thing)
import B
import Effect.Console (log)

-- Not an error as although we have `thing` in scope from both A and B, it is
-- imported explicitly from A, giving it a resolvable solution.
what :: Boolean -> ?test
what true = thing
what false = zing

main = log "Done"
