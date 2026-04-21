module Main where

import Prelude
import Effect.Console (log)

subtractOne :: Int -> Int
subtractOne = (_ - 1)

addOne :: Int -> Int
addOne = ?test

named :: Int -> Int
named = (_ `sub` 1)

main = log "Done"
