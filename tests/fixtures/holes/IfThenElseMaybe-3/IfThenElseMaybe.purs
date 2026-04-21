module Main where

import Prelude
import Effect.Console (log)

data Maybe a = Nothing | Just a

test1 = if true then Just 10 else Nothing

test2 = ?test

main = log "Done"
