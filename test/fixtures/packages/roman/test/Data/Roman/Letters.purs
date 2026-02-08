module Test.Data.Roman.Letters where

import Prelude
import Data.Map (fromFoldable)
import Data.Roman.Letters (LetterTriplet(..), toSymbols, fromLetters)
import Data.Roman.Symbols (SymbolsTable(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Test.Assert (assertEqual)

testLetters :: Effect Unit
testLetters = do
  assertEqual
    { actual: fromLetters []
    , expected: []
    }
  assertEqual
    { actual: fromLetters [ "I", "V" ]
    , expected: []
    }
  assertEqual
    { actual: fromLetters [ "I", "V", "X" ]
    , expected: [ LetterTriplet "I" "V" "X" 1 ]
    }
  assertEqual
    { actual: fromLetters [ "I", "V", "X", "L" ]
    , expected: [ LetterTriplet "I" "V" "X" 1 ]
    }
  assertEqual
    { actual: fromLetters [ "I", "V", "X", "L", "C" ]
    , expected:
        [ LetterTriplet "I" "V" "X" 1
        , LetterTriplet "X" "L" "C" 10
        ]
    }
  assertEqual
    { actual: toSymbols $ LetterTriplet "I" "V" "X" 1
    , expected:
        SymbolsTable
          ( fromFoldable
              [ Tuple "I" 1
              , Tuple "IV" 4
              , Tuple "V" 5
              , Tuple "IX" 9
              , Tuple "X" 10
              ]
          )
    }
  assertEqual
    { actual: toSymbols $ LetterTriplet "X" "L" "C" 10
    , expected:
        SymbolsTable
          ( fromFoldable
              [ Tuple "X" 10
              , Tuple "XL" 40
              , Tuple "L" 50
              , Tuple "XC" 90
              , Tuple "C" 100
              ]
          )
    }
