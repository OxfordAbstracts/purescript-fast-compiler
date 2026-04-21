module Main where

import Effect.Console (log)
import Partial.Unsafe (unsafePartial)

data X = Prim

f :: Partial => Int -> ?test
f 0 = 0

f' = unsafePartial f

main = log "Done"
