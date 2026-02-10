module Test.Data.Roman.Symbols where

import Prelude

import Data.Map (fromFoldable)
import Data.Maybe (Maybe(..))
import Data.Roman.Symbols (getSymbols, getSymbolValues, lookupSymbol, reverseLookupSymbol, SymbolsTable(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Prim as Test.Data.Roman
import Test.Assert (assertEqual)

symbolsTableFixture :: SymbolsTable
symbolsTableFixture =
  SymbolsTable
    ( fromFoldable
        [ Tuple "a" 1
        , Tuple "b" 2
        , Tuple "c" 3
        ]
    )

testSymbols :: Effect Unit
testSymbols = do
  assertEqual
    { actual: getSymbols symbolsTableFixture
    , expected: [ "a", "b", "c" ]
    }
  assertEqual
    { actual: getSymbolValues symbolsTableFixture
    , expected: [ 1, 2, 3 ]
    }
  assertEqual
    { actual: lookupSymbol "a" symbolsTableFixture
    , expected: Just 1
    }
  assertEqual
    { actual: lookupSymbol "d" symbolsTableFixture
    , expected: Nothing
    }
  assertEqual
    { actual: reverseLookupSymbol 1 symbolsTableFixture
    , expected: Just "a"
    }
  assertEqual
    { actual: reverseLookupSymbol 4 symbolsTableFixture
    , expected: Nothing
    }
