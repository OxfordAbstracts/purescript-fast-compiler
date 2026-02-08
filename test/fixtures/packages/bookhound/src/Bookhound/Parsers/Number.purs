module Bookhound.Parsers.Number (int, double, posInt, negInt, unsignedInt, hexInt) where

import Prelude

import Bookhound.Parser (Parser, withErrorN)
import Bookhound.ParserCombinators (is, oneOf, (->>-), (|+), (|?), (||+))
import Bookhound.Parsers.Char (dash, digit, dot, hexDigit, plus)
import Control.Alt ((<|>))
import Data.Int as Int
import Data.Maybe (fromJust)
import Data.Number as Number
import Partial.Unsafe (unsafePartial)

hexInt :: Parser Int
hexInt = withErrorN (-1) "Hex Int" $ unsafeReadInt
  <$> (is "0x" ->>- (|+) hexDigit)

unsignedInt :: Parser Int
unsignedInt = withErrorN (-1) "Unsigned Int" $ unsafeReadInt
  <$> (||+) digit

posInt :: Parser Int
posInt = withErrorN (-1) "Positive Int" $ unsafeReadInt
  <$> ((|?) plus *> (||+) digit)

negInt :: Parser Int
negInt = withErrorN (-1) "Negative Int" $ unsafeReadInt
  <$> (dash ->>- (||+) digit)

int :: Parser Int
int = withErrorN (-1) "Int" $ negInt <|> posInt

double :: Parser Number
double = withErrorN (-1) "Double" $ unsafeReadNumber
  <$> int ->>- (decimals ->>- (|?) expn <|> expn)
  where
  decimals = dot ->>- unsignedInt
  expn = oneOf [ 'e', 'E' ] ->>- int

unsafeReadInt :: String -> Int
unsafeReadInt x = unsafePartial $ fromJust $ Int.fromString x

unsafeReadNumber :: String -> Number
unsafeReadNumber x = unsafePartial $ fromJust $ Number.fromString x
