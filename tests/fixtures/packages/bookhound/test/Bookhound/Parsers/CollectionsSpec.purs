module Bookhound.Parsers.CollectionsSpec where

import TestPrelude

import Bookhound.Parser (runParser)
import Bookhound.ParserCombinators (is)
import Bookhound.Parsers.Char (alpha)
import Bookhound.Parsers.Collections (listOf, mapOf)
import Bookhound.Utils.Char (isAlpha)
import Data.Array (filter)
import Data.Either (Either(..))
import Data.Foldable (intercalate)
import Data.Map as Map
import Data.String.CodeUnits (fromCharArray)
import Data.String.CodeUnits as String
import Data.Tuple.Nested (type (/\), (/\))

spec :: Spec Unit
spec = describe "Bookhound.Parsers.Collections" $ do

  describe "listOf"
    $ prop "parses a list provided the element parser"
    $ \(x :: Array Char) ->
        runParser (listOf alpha)
          ( "["
              <> intercalate ", "
                (fromCharArray <<< pure <$> filter isAlpha x)
              <> "]"
          )
          === Right (filter isAlpha x)

  describe "mapOf"
    $ prop "parses a map provided the key and value parsers"
    $ \(x :: Array (Char /\ Char)) ->
        runParser (mapOf (is ":") alpha alpha)
          ( "{"
              <> intercalate ", " (showMapEntry <$> filter areAlpha' x)
              <> "}"
          )
          === Right (Map.fromFoldable $ filter areAlpha' x)

showMapEntry :: (Char /\ Char) -> String
showMapEntry (x /\ y) =
  String.singleton x <> ": " <> String.singleton y

areAlpha' :: (Char /\ Char) -> Boolean
areAlpha' (x /\ y) = isAlpha x && isAlpha y
