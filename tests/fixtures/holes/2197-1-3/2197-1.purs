module Main where

import Effect.Console
import Prim as P

type Number = P.Number
type Test = {}

z :: ?test
z = 0.0

main = log "Done"
