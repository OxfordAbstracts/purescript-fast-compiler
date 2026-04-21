module Main (thing, main, module A) where

import A
import Effect.Console (log)

thing :: Int
thing = ?test

main = log "Done"
