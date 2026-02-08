module Bookhound.Parsers.NumberSpec where

import TestPrelude

import Bookhound.Parser (runParser)
import Bookhound.Parsers.Number (int, negInt, posInt)
import Data.Either (Either(..))

spec :: Spec Unit
spec = describe "Bookhound.Parsers.Number" $ do

  describe "posInt"
    $ prop "parses a positive Int"
    $ \(x :: PositiveInt) ->
        runParser posInt (show $ unwrap x)
          === Right (unwrap x)

  describe "negInt"
    $ prop "parses a negative Int"
    $ \(x :: NegativeInt) ->
        runParser negInt (show $ unwrap x)
          === Right (unwrap x)

  describe "int"
    $ prop "parses an Int"
    $ \(x :: Int) ->
        runParser int (show x)
          === Right x
