module Test.Data.Roman.Convert where

import Prelude
import Data.Roman.Convert (toRoman, fromRoman)
import Data.Tuple (Tuple(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Test.Assert (assertEqual)
import Data.String.Common (split)
import Data.String.Pattern (Pattern(..))
import Node.Encoding (Encoding(..))
import Data.Array (range, zip)
import Node.FS.Sync (readTextFile)

testConvert :: Effect Unit
testConvert = do
  csv <- readTextFile UTF8 "test/numerals.csv"
  void (traverse convert (zip (range 1 150) (split (Pattern ",") csv)))
  where
  convert (Tuple int numeral) = do
    assertEqual
      { actual: toRoman int
      , expected: numeral
      }
    assertEqual
      { actual: fromRoman numeral
      , expected: int
      }
