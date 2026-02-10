module Data.Roman.Symbols
  ( SymbolsTable(..)
  , getSymbols
  , getSymbolValues
  , lookupSymbol
  , reverseLookupSymbol
  ) where

import Prelude
import Data.Map (Map, lookup, empty, union)
import Data.Map.Eager (keys, values, reverseLookup)
import Data.Maybe (Maybe)

-- | `SymbolsTable` represents a mapping of Roman numerals to integer values
newtype SymbolsTable
  = SymbolsTable (Map String Int)

instance eqSymbolsTable :: Eq SymbolsTable where
  eq (SymbolsTable x) (SymbolsTable y) = eq x y

instance showSymbolsTable :: Show SymbolsTable where
  show (SymbolsTable x) = show x

instance monoidSymbolsTable :: Monoid SymbolsTable where
  mempty = SymbolsTable empty

instance semigroupSymbolsTable :: Semigroup SymbolsTable where
  append (SymbolsTable x) (SymbolsTable y) = (SymbolsTable (union x y))

getSymbols :: SymbolsTable -> Array String
getSymbols (SymbolsTable symbolsTable) = keys symbolsTable

getSymbolValues :: SymbolsTable -> Array Int
getSymbolValues (SymbolsTable symbolsTable) = values symbolsTable

lookupSymbol :: String -> SymbolsTable -> Maybe Int
lookupSymbol key (SymbolsTable symbolsTable) = lookup key symbolsTable

reverseLookupSymbol :: Int -> SymbolsTable -> Maybe String
reverseLookupSymbol key (SymbolsTable symbolsTable) = reverseLookup key symbolsTable
