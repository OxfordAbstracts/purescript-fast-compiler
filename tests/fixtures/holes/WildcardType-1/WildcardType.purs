module Main where

import Prelude
import Effect.Console (log)

f1 :: (_ -> _) -> _
f1 g = ?test

f2 :: _ -> _
f2 _ = "Done"

main = log $ f1 f2
