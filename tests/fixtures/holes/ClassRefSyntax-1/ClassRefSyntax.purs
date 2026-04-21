module Main where

import Lib (class X, go)
import Effect.Console (log)

go' :: forall a. X a => a -> a
go' = ?test

main = log "Done"
