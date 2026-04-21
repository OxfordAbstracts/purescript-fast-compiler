module Main where

import Effect.Console
import Prim (Int)

type Number = Int

z :: Number
z = ?test

main = log "Done"
