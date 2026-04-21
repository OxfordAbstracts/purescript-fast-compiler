module Main where

import Effect.Console (log)

fns = \f -> if f true then f else \x -> x

not = ?test

main = log "Done"
