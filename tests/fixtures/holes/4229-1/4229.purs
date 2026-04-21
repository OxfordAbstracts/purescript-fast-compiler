module Main where

import Effect.Console (log)
import Partial.Unsafe (unsafePartial)

data X = Prim

f :: Partial => Int -> Int
f 0 = ?test

f' = unsafePartial f

main = log "Done"
