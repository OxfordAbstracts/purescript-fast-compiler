module Main (thing, main, module A) where

import A
import Effect.Console (log)

thing :: ?test
thing = 2

main = log "Done"
