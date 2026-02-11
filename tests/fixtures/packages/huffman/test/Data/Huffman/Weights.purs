module Test.Data.Huffman.Weights where

import Prelude
import Data.Map (fromFoldable)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Data.Huffman.Occurrences (countOccurrences)
import Data.Huffman.Letter (Letter(..))
import Data.Huffman.Weights (Weights(..), fromOccurrences)
import Test.Assert (assertEqual)

testWeights :: Effect Unit
testWeights = do
  assertEqual
    { actual: fromOccurrences $ countOccurrences "ab"
    , expected:
        Weights
          $ fromFoldable
              [ Tuple (Letter 'a') 0.5
              , Tuple (Letter 'b') 0.5
              ]
    }
