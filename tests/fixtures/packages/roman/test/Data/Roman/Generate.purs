module Test.Data.Roman.Generate where

import Prelude
import Data.Map (empty, fromFoldable)
import Data.Roman.Generate (generateSymbols)
import Data.Roman.Symbols (SymbolsTable(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Test.Assert (assertEqual)

testGenerate :: Effect Unit
testGenerate = do
  assertEqual
    { actual: generateSymbols []
    , expected: SymbolsTable empty
    }
  assertEqual
    { actual: generateSymbols [ "I", "V", "X", "L", "C", "D", "M", "V*", "X*" ]
    , expected:
        SymbolsTable
          ( fromFoldable
              [ Tuple "I" 1
              , Tuple "IV" 4
              , Tuple "V" 5
              , Tuple "IX" 9
              , Tuple "X" 10
              , Tuple "XL" 40
              , Tuple "L" 50
              , Tuple "XC" 90
              , Tuple "C" 100
              , Tuple "CD" 400
              , Tuple "D" 500
              , Tuple "CM" 900
              , Tuple "M" 1000
              , Tuple "MV*" 4000
              , Tuple "V*" 5000
              , Tuple "MX*" 9000
              , Tuple "X*" 10000
              ]
          )
    }
