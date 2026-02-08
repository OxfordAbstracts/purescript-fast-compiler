module Data.Roman.Generate
  ( generateSymbols
  ) where

import Prelude
import Data.Array (foldl)
import Data.Map (empty)
import Data.Roman.Letters (toSymbols, fromLetters)
import Data.Roman.Symbols (SymbolsTable(..))

generateSymbols :: Array String -> SymbolsTable
generateSymbols letters = foldl joinSets (SymbolsTable empty) (fromLetters letters)
  where
  joinSets acc x = append acc $ toSymbols x
