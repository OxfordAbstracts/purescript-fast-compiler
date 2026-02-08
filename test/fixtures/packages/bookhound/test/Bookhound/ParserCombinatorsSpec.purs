module Bookhound.ParserCombinatorsSpec where

import TestPrelude

import Bookhound.Parser (ParseError(..), ParseResult(..), Parser, anyOf, anyChar, parse)
import Bookhound.ParserCombinators (between, is, many, manySepBy, maybeBetween, maybeSurroundedBy, multiple, multipleSepBy, some, someSepBy, surroundedBy, times, (->>-), (|*), (|+), (|?))
import Bookhound.Utils.Array ((..))
import Data.Array (cons, head, reverse)
import Data.Array as Array
import Data.Maybe (optional)
import Data.String as String
import Data.String.CodeUnits (fromCharArray, toCharArray)

spec :: Spec Unit
spec = describe "Bookhound.ParserCombinators" $ do

  describe "times"
    $ prop "applies a parser n times sequentially"
    $ \x (n :: SmallInt) -> parse (times (unwrap n) anyChar) x
        ===
          if String.length x >= unwrap n then
            Result (String.drop (unwrap n) x)
              (toCharArray $ String.take (unwrap n) x)
          else
            Error UnexpectedEof

  describe "optional"
    $ prop "applies a parser 1 or 0 times"
    $ \x -> parse (optional anyChar) x
        === (head <$> parseTimes anyChar [ 0, 1 ] x)

  describe "many"
    $ prop "applies a parser any number of times"
    $ \x -> parse (many anyChar) x
        === parseTimes anyChar (0 .. (String.length x + 10)) x

  describe "some"
    $ prop "applies a parser at least once"
    $ \x -> parse (some anyChar) x
        === parseTimes anyChar (1 .. max 1 (String.length x + 10)) x

  describe "multiple"
    $ prop "applies a parser at least twice"
    $ \x -> parse (multiple anyChar) x
        === parseTimes anyChar (2 .. max 2 (String.length x + 10)) x

  describe "between"
    $ prop "applies a parser surrounded by 2 parsers"
    $ \x (y :: Char) (z :: Char) ->
        parse (between (is y) (is z) anyChar) x
          === parse (is y *> anyChar <* is z) x

  describe "maybeBetween"
    $ prop "applies a parser surrounded by 2 optional parsers"
    $ \x (y :: Char) (z :: Char) ->
        parse (maybeBetween (is y) (is z) anyChar) x
          === parse (((|?) $ is y) *> anyChar <* ((|?) $ is z)) x

  describe "surroundedBy"
    $ prop "applies a parser surrounded by a parser"
    $ \x (y :: Char) ->
        parse (surroundedBy (is y) anyChar) x
          === parse (is y *> anyChar <* is y) x

  describe "maybeSurroundedBy"
    $ prop "applies a parser surrounded by a optional parsers"
    $ \x (y :: Char) ->
        parse (maybeSurroundedBy (is y) anyChar) x
          === parse (((|?) $ is y) *> anyChar <* ((|?) $ is y)) x

  describe "manySepBy"
    $ prop "applies a parser separated by a parser any number of times"
    $ \x (y :: Char) ->
        parse (manySepBy (is y) anyChar) x
          === parse
            ( append
                <$> (map Array.fromFoldable ((|?) anyChar))
                <*> ((|*) (is y *> anyChar))
            )
            x

  describe "someSepBy"
    $ prop "applies a parser separated by a parser at least once"
    $ \x (y :: Char) ->
        parse (someSepBy (is y) anyChar) x
          === parse (cons <$> anyChar <*> ((|*) (is y *> anyChar))) x

  describe "multipleSepBy"
    $ prop "applies a parser separated by a parser at least twice"
    $ \x (y :: Char) ->
        parse (multipleSepBy (is y) anyChar) x
          === parse (cons <$> anyChar <*> ((|+) (is y *> anyChar))) x

  describe "parseAppend"
    $ prop "concats results of 2 parsers that can be converted to Strings"
    $ \x (y :: Char) (z :: Char) ->
        parse (is y ->>- is z) x
          === parse (is $ fromCharArray [ y, z ]) x

parseTimes :: forall a. Parser a -> Array Int -> String -> ParseResult (Array a)
parseTimes p ns = parse $ anyOf (flip times p <$> reverse ns)
