module Webb.Parsing.String
  ( alphaChar
  , anyCase
  , fromChars
  , letterChar
  , lowerCase
  , lowerChar
  , numChar
  , upperCase
  , upperChar
  )
  where

import Parsing
import Prelude

import Control.Alt ((<|>))
import Data.Array as A
import Data.String as Str
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (class Foldable, sequence)
import Parsing.Combinators (try)
import Parsing.String as PStr
import Parsing.String.Basic as PB


{- Useful string parsers.
-}

type Parser m = ParserT String m

-- Parse the string with any case for its characters.
anyCase :: forall m. String -> Parser m String
anyCase str = try do
  let lowers = Str.split (Str.Pattern "") str
      parsers = lowers <#> lowerOrUpper
  chars <- sequence parsers
  pure $ Str.joinWith "" chars
  where 
  lowerOrUpper char = try do
    let upper = Str.toUpper char
        lower = Str.toLower char
    try (PStr.string lower) <|> try (PStr.string upper)

-- Parse the string with only uppercase for its characters.
upperCase :: forall m. String -> Parser m String
upperCase str = try do
  let parser = PStr.string $ Str.toUpper str
  parser

-- Parse the string with only lowercase for its characters.
lowerCase :: forall m. String -> Parser m String
lowerCase str = try do
  let parser = PStr.string $ Str.toLower str
  parser
  
fromChars :: forall f. Foldable f => f Char -> String
fromChars chars = fromCharArray $ A.fromFoldable chars

letterChar :: forall m. Parser m String
letterChar = try do
  char <- PB.letter
  pure $ fromChars [char]
  
upperChar :: forall m. Parser m String
upperChar = do
  char <- PB.upper
  pure $ fromChars [ char ]

lowerChar :: forall m. Parser m String
lowerChar = do
  char <- PB.lower
  pure $ fromChars [ char ]
  
alphaChar :: forall m. Parser m String
alphaChar = letterChar
  
numChar :: forall m. Parser m String
numChar = try do 
  char <- PB.digit
  pure $ fromChars [ char ]