module Main where

import Prelude

import Effect.Console (log)

class Convert a b | a -> b where
  convert :: a -> b

type Words = String

instance convertSB :: Convert Int Words where
  convert 0 = "Nope"
  convert _ = "Done"

main = ?test $ convert 1
