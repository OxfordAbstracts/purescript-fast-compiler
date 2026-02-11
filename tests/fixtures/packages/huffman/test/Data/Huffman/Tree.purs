module Test.Data.Huffman.Tree where

import Prelude
import Effect (Effect)
import Data.Huffman.Occurrences (countOccurrences)
import Data.Huffman.Letter (Letter(..))
import Data.Huffman.Tree (HuffmanTree(..), fromWeights)
import Data.Huffman.Weights (fromOccurrences)
import Test.Assert (assertEqual)

tree :: String -> HuffmanTree
tree = fromWeights <<< fromOccurrences <<< countOccurrences

testTree :: Effect Unit
testTree = do
  assertEqual
    { actual: tree ""
    , expected: Node [] 1.0
    }
  assertEqual
    { actual: tree "a"
    , expected: Node [ Leaf (Letter 'a') 1.0 ] 1.0
    }
  assertEqual
    { actual: tree "ab"
    , expected:
        Node
          [ Leaf (Letter 'a') 0.5
          , Leaf (Letter 'b') 0.5
          ]
          1.0
    }
  assertEqual
    -- cspell:disable-next-line
    { actual: tree "abcc"
    , expected:
        Node
          [ Node
              [ Leaf (Letter 'a') 0.25
              , Leaf (Letter 'b') 0.25
              ]
              0.5
          , Leaf (Letter 'c') 0.5
          ]
          1.0
    }
  assertEqual
    { actual: tree "abcdefgh"
    , expected:
        Node
          [ Node
              [ Node
                  [ Leaf (Letter 'c') 0.125
                  , Leaf (Letter 'd') 0.125
                  ]
                  0.25
              , Node
                  [ Leaf (Letter 'a') 0.125
                  , Leaf (Letter 'b') 0.125
                  ]
                  0.25
              ]
              0.5
          , Node
              [ Node
                  [ Leaf (Letter 'g') 0.125
                  , Leaf (Letter 'h') 0.125
                  ]
                  0.25
              , Node
                  [ Leaf (Letter 'e') 0.125
                  , Leaf (Letter 'f') 0.125
                  ]
                  0.25
              ]
              0.5
          ]
          1.0
    }
