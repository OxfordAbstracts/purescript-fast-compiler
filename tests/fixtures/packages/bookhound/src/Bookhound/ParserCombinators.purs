module Bookhound.ParserCombinators
  ( class IsMatch
  , is
  , isNot
  , inverse
  , char
  , string
  , oneOf
  , noneOf
  , times
  , some
  , many
  , multiple
  , manyChar
  , someChar
  , multipleChar
  , applyCons
  , applyTuple
  , between
  , maybeBetween
  , surroundedBy
  , maybeSurroundedBy
  , manySepBy
  , someSepBy
  , multipleSepBy
  , sepByOp
  , sepByOps
  , manyEndBy
  , someEndBy
  , multipleEndBy
  , parseAppend
  , withErrorFlipped
  , timesFlipped
  , (<?>)
  , (<#>)
  , (<&>)
  , (<:>)
  , (</\>)
  , (->>-)
  , (|?)
  , (|*)
  , (|+)
  , (|++)
  , (||*)
  , (||+)
  , (||++)
  ) where

import Prelude hiding (between)

import Bookhound.Parser (Parser, allOf, anyOf, both, anyChar, except, satisfy, withError)
import Bookhound.ParserCombinators.List as List
import Bookhound.Utils.Array ((..))
import Bookhound.Utils.String (class ToString, charTraverse, toString)
import Control.Apply (lift2)
import Data.Array (cons)
import Data.Array as Array
import Data.Bifunctor (bimap, rmap)
import Data.Maybe (maybe, optional)
import Data.String.CodeUnits (fromCharArray)
import Data.String.CodeUnits as String
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\))

class IsMatch a where
  is :: a -> Parser a
  isNot :: a -> Parser a
  inverse :: Parser a -> Parser a

instance IsMatch Char where
  is = isMatch (==) anyChar
  isNot = isMatch (/=) anyChar
  inverse = except anyChar

else instance IsMatch String where
  is = charTraverse is
  isNot = charTraverse isNot
  inverse = except $ (||*) anyChar

isMatch :: forall a. (a -> a -> Boolean) -> Parser a -> a -> Parser a
isMatch cond ma c1 = satisfy (cond c1) ma

char :: Char -> Parser Char
char = is

string :: String -> Parser String
string = is

oneOf :: forall a. IsMatch a => Array a -> Parser a
oneOf = anyOf <<< map is

noneOf :: forall a. IsMatch a => Array a -> Parser a
noneOf = allOf <<< map isNot

-- Frequency combinators
many :: forall a. Parser a -> Parser (Array a)
many = map Array.fromFoldable <<< List.many

some :: forall a. Parser a -> Parser (Array a)
some = map Array.fromFoldable <<< List.some

multiple :: forall a. Parser a -> Parser (Array a)
multiple = map Array.fromFoldable <<< List.multiple

optionalChar :: Parser Char -> Parser String
optionalChar = map (maybe mempty String.singleton) <<< optional

manyChar :: Parser Char -> Parser String
manyChar = map fromCharArray <<< many

someChar :: Parser Char -> Parser String
someChar = map fromCharArray <<< some

multipleChar :: Parser Char -> Parser String
multipleChar = map fromCharArray <<< multiple

times :: forall a. Int -> Parser a -> Parser (Array a)
times n p
  | n < 1 = pure []
  | otherwise = sequence $ p <$ (1 .. n)

-- Sep by combinators
manySepBy :: forall a b. Parser a -> Parser b -> Parser (Array b)
manySepBy sep p = Array.fromFoldable <$> List.manySepBy sep p

someSepBy :: forall a b. Parser a -> Parser b -> Parser (Array b)
someSepBy sep p = Array.fromFoldable <$> List.someSepBy sep p

multipleSepBy :: forall a b. Parser a -> Parser b -> Parser (Array b)
multipleSepBy sep p = Array.fromFoldable <$> List.multipleSepBy sep p

-- Sep by ops combinators
sepByOps :: forall a b. Parser a -> Parser b -> Parser (Array a /\ Array b)
sepByOps sep p = bimap Array.fromFoldable Array.fromFoldable
  <$> List.sepByOps sep p

sepByOp :: forall a b. Parser a -> Parser b -> Parser (a /\ Array b)
sepByOp sep p = rmap Array.fromFoldable
  <$> List.sepByOp sep p

-- End by combinators
manyEndBy :: forall a b. Parser a -> Parser b -> Parser (Array b)
manyEndBy end p = Array.fromFoldable <$> List.manyEndBy end p

someEndBy :: forall a b. Parser a -> Parser b -> Parser (Array b)
someEndBy end p = Array.fromFoldable <$> List.someEndBy end p

multipleEndBy :: forall a b. Parser a -> Parser b -> Parser (Array b)
multipleEndBy end p = Array.fromFoldable <$> List.multipleEndBy end p

-- Between combinators
between :: forall a b c. Parser a -> Parser b -> Parser c -> Parser c
between start end p = start *> p <* end

maybeBetween :: forall a b c. Parser a -> Parser b -> Parser c -> Parser c
maybeBetween p p' = between (optional p) (optional p')

surroundedBy :: forall a b. Parser a -> Parser b -> Parser b
surroundedBy p = between p p

maybeSurroundedBy :: forall a b. Parser a -> Parser b -> Parser b
maybeSurroundedBy = surroundedBy <<< optional

parseAppend
  :: forall a b
   . ToString a
  => ToString b
  => Parser a
  -> Parser b
  -> Parser String
parseAppend p1 p2 = append <$> map toString p1 <*> map toString p2

applyTuple :: forall f a b. Apply f => f a -> f b -> f (a /\ b)
applyTuple = lift2 Tuple

applyCons :: forall f a. Apply f => f a -> f (Array a) -> f (Array a)
applyCons = lift2 cons

withErrorFlipped :: forall t31. Parser t31 -> String -> Parser t31
withErrorFlipped = flip withError

timesFlipped :: forall a. Parser a -> Int -> Parser (Array a)
timesFlipped = flip times

-- Parser Binary Operators
infixl 6 timesFlipped as <#>

infixl 6 withErrorFlipped as <?>

infixl 6 both as <&>

infixl 6 parseAppend as ->>-

-- Apply Binary Operators
infixl 6 applyTuple as </\>

infixl 6 applyCons as <:>

-- Frequency Unary Operators
infix 0 optional as |?

infix 0 many as |*

infix 0 some as |+

infix 0 multiple as |++

-- Char Frequency Unary Operators
infix 0 optionalChar as ||?

infix 0 manyChar as ||*

infix 0 someChar as ||+

infix 0 multipleChar as ||++
