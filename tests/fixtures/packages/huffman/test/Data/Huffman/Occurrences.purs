module Test.Data.Huffman.Occurrences where

import Prelude
import Data.Map (empty, singleton, fromFoldable)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Data.Huffman.Occurrences (Occurrences(..), countOccurrences)
import Data.Huffman.Letter (Letter(..))
import Test.Assert (assertEqual)

testOccurrences :: Effect Unit
testOccurrences = do
  assertEqual
    { actual: countOccurrences ""
    , expected: Occurrences empty
    }
  assertEqual
    { actual: countOccurrences "a"
    , expected: Occurrences $ singleton (Letter 'a') 1
    }
  assertEqual
    { actual: countOccurrences "ab"
    , expected:
        Occurrences
          $ fromFoldable
              [ Tuple (Letter 'a') 1
              , Tuple (Letter 'b') 1
              ]
    }
  assertEqual
    { actual: countOccurrences "abb"
    , expected:
        Occurrences
          $ fromFoldable
              [ Tuple (Letter 'a') 1
              , Tuple (Letter 'b') 2
              ]
    }
