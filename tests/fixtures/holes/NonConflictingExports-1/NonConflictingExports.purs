-- No failure here as the export `thing` only refers to Main.thing
module Main (thing, main) where

import A
import Effect.Console (log)

thing :: Int
thing = ?test

main = log "Done"
