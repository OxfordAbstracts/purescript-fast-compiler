module Test.Main where

import Prelude

import Effect (Effect)
import Test.Router.Parser (testParser)
import Test.Unit.Main (runTest)

main :: Effect Unit
main = runTest do
  testParser
