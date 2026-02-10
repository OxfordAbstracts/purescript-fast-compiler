module Bookhound.ParserCombinators.List
  ( many
  , some
  , multiple
  , manySepBy
  , someSepBy
  , multipleSepBy
  , manyEndBy
  , someEndBy
  , multipleEndBy
  , sepByOp
  , sepByOps
  , (|?)
  , (|*)
  , (|+)
  , (|++)
  ) where

import Prelude

import Bookhound.Parser (Parser, satisfy)
import Bookhound.Utils.List (hasMultiple, hasSome) as List
import Control.Alt ((<|>))
import Control.Apply (lift2)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..), optional)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (type (/\), (/\))

-- Frequency combinators
many :: forall a. Parser a -> Parser (List a)
many p = (p >>= \x -> pure x <:> many p)
  <|> pure mempty

some :: forall a. Parser a -> Parser (List a)
some = satisfy List.hasSome <<< many

multiple :: forall a. Parser a -> Parser (List a)
multiple = satisfy List.hasMultiple <<< many

-- Sep by combinators
sepBy
  :: forall a b
   . (Parser b -> Parser (Maybe b))
  -> (Parser b -> Parser (List b))
  -> Parser a
  -> Parser b
  -> Parser (List b)
sepBy freq1 freq2 sep p =
  maybeCons <$> freq1 p <*> freq2 (sep *> p)
  where
  maybeCons Nothing = identity
  maybeCons (Just x) = Cons x

manySepBy :: forall a b. Parser a -> Parser b -> Parser (List b)
manySepBy = sepBy optional many

someSepBy :: forall a b. Parser a -> Parser b -> Parser (List b)
someSepBy = sepBy (map Just) many

multipleSepBy :: forall a b. Parser a -> Parser b -> Parser (List b)
multipleSepBy = sepBy (map Just) some

-- Sep by ops combinators
sepByOps :: forall a b. Parser a -> Parser b -> Parser (List a /\ List b)
sepByOps sepP p = do
  x <- p
  ys <- (|+) (Tuple <$> sepP <*> p)
  pure $ map fst ys /\ x : map snd ys

sepByOp :: forall a b. Parser a -> Parser b -> Parser (a /\ List b)
sepByOp sepP p = do
  x1 <- p
  sep <- sepP
  x2 <- p
  xs <- (|*) (sepP *> p)
  pure (sep /\ x1 : x2 : xs)

-- End by combinators
endBy
  :: forall a b
   . (Parser b -> Parser (Maybe b))
  -> (Parser b -> Parser (List b))
  -> Parser a
  -> Parser b
  -> Parser (List b)
endBy freq1 freq2 sep p =
  sepBy freq1 freq2 sep p <* sep

manyEndBy :: forall a b. Parser a -> Parser b -> Parser (List b)
manyEndBy = endBy optional many

someEndBy :: forall a b. Parser a -> Parser b -> Parser (List b)
someEndBy = endBy (map Just) many

multipleEndBy :: forall a b. Parser a -> Parser b -> Parser (List b)
multipleEndBy = endBy (map Just) some


applyCons :: forall f a. Apply f => f a -> f (List a) -> f (List a)
applyCons = lift2 Cons

-- Apply Binary Operators
infixl 6 applyCons as <:>

-- Frequency Unary Operators
infix 0 optional as |?

infix 0 many as |*

infix 0 some as |+

infix 0 multiple as |++
