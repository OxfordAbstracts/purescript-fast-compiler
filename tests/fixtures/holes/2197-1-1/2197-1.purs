module Main where

import Effect.Console
import Prim as P

type Number = P.Number
type Test = {}

z :: Number
z = ?test

main = log "Done"
