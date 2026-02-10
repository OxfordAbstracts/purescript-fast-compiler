module Test.Main where

import Prelude
import Effect (Effect)
import Test.Data.Roman.Convert (testConvert)
import Test.Data.Roman.Generate (testGenerate)
import Test.Data.Roman.Letters (testLetters)
import Test.Data.Roman.Symbols (testSymbols)

main :: Effect Unit
main = do
  testConvert
  testGenerate
  testLetters
  testSymbols
