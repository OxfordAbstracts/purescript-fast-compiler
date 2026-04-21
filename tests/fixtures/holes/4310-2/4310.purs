module Main where

import Effect.Console (log)
import Lib

main = do
  let q = runTest (4 /\ 4)
  ?test "Done"
