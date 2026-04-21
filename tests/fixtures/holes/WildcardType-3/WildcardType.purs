module Main where

import Prelude
import Effect.Console (log)

f1 :: (_ -> _) -> _
f1 g = g 1

f2 :: ?test -> _
f2 _ = "Done"

main = log $ f1 f2
