module Main where

import Prelude
import Effect.Console (log)

data Maybe a = Nothing | Just a

test1 = ?test

test2 = if true then Nothing else Just 10

main = log "Done"
