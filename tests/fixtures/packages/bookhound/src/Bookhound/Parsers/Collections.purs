module Bookhound.Parsers.Collections (collOf, listOf, tupleOf, mapOf) where

import Prelude

import Bookhound.Parser (Parser, satisfy, withErrorN)
import Bookhound.ParserCombinators (manySepBy, (</\>))
import Bookhound.Parsers.Char (closeCurly, closeParens, closeSquare, comma, openCurly, openParens, openSquare)
import Bookhound.Parsers.String (maybeBetweenSpacing)
import Bookhound.Utils.Array (hasMultiple)
import Data.Map (Map)
import Data.Map as Map

collOf :: forall a b c d. Parser a -> Parser b -> Parser c -> Parser d -> Parser (Array d)
collOf start end sep elemParser = start *> elemsParser <* end
  where
  elemsParser = manySepBy sep $ maybeBetweenSpacing elemParser

listOf :: forall a. Parser a -> Parser (Array a)
listOf = withErrorN (-1) "List"
  <<< collOf openSquare closeSquare comma

tupleOf :: forall a. Parser a -> Parser (Array a)
tupleOf = withErrorN (-1) "Tuple"
  <<< satisfy hasMultiple
  <<< collOf openParens closeParens comma

mapOf :: forall a b c. Ord b => Parser a -> Parser b -> Parser c -> Parser (Map b c)
mapOf sep p1 p2 = withErrorN (-1) "Map "
  $ Map.fromFoldable
      <$> collOf openCurly closeCurly comma mapEntry
  where
  mapEntry = (p1 <* maybeBetweenSpacing sep) </\> p2
