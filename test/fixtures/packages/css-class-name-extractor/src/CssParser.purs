module CssClassNameExtractor.CssParser where

import Prelude

import Control.Alt ((<|>))
import Data.Array as Data.Array
import Data.Either (Either)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.List (List, toUnfoldable, (:))
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.String (trim)
import Data.String.CodeUnits (fromCharArray, singleton)
import Data.Traversable (traverse)
import Parsing (ParseError, Parser, runParser)
import Parsing.Combinators (choice, many, many1, manyTill, optionMaybe, optional, sepBy, try)
import Parsing.String (char, string)
import Parsing.String.Basic (noneOf, skipSpaces)
import Parsing.Token (digit, letter)

firstChar :: Parser String Char
firstChar = letter <|> char '_' <|> char '-'

restChar :: Parser String Char
restChar = firstChar <|> digit

identifier :: Parser String String
identifier = do
  first <- map singleton firstChar
  rest <- map (restToString) (many restChar)
  pure (first <> rest)
  where
  restToString :: List Char -> String
  restToString chars = fromCharArray (Data.Array.fromFoldable chars)

quotedString :: Parser String String
quotedString = do
  char '"' *> pure unit
  content <- many (noneOf [ '"' ])
  char '"' *> pure unit
  fromCharArray (Data.Array.fromFoldable content) # pure

attributeOperator :: Parser String String
attributeOperator =
  string "="
    <|> string "~="
    <|> string "|="
    <|> string "^="
    <|> string "$="
    <|> string "*="

data AttributeSelector
  = AttributeEquals String String
  | AttributeExists String
  | AttributeContains String String
  | AttributeStartWith String String
  | AttributeEndWith String String

derive instance Generic AttributeSelector _
instance Eq AttributeSelector where
  eq = genericEq

instance Show AttributeSelector where
  show = genericShow

makeAttributeSelector :: String -> String -> String -> AttributeSelector
makeAttributeSelector op name value = case op of
  "=" -> AttributeEquals name value
  "~=" -> AttributeContains name value
  "^=" -> AttributeStartWith name value
  "$=" -> AttributeEndWith name value
  _ -> AttributeEquals name value

data CombinatorType
  = Child
  | Adjacent
  | Sibling
  | Descendant

derive instance Generic CombinatorType _
instance Eq CombinatorType where
  eq = genericEq

instance Show CombinatorType where
  show = genericShow

combinatorType :: Parser String CombinatorType
combinatorType = (char '>' $> Child)
  <|> (char '+' $> Adjacent)
  <|> (char '~' $> Sibling)
  <|> pure Descendant

newtype Selector = Selector SelectorF
data SelectorF
  = Type String
  | Class String
  | Id String
  | Universal
  | Attribute AttributeSelector
  | Combinator CombinatorType Selector

derive instance Generic SelectorF _
derive instance Generic Selector _

derive instance Eq SelectorF
derive instance Eq Selector

instance Show Selector where
  show (Selector s) = case s of
    Type str -> "Type " <> show str
    Class str -> "Class " <> show str
    Id str -> "Id " <> show str
    Universal -> "Universal"
    Attribute attr -> "Attribute " <> show attr
    Combinator combType sel ->
      "Combinator " <> show combType <> " " <> show sel

instance Show SelectorF where
  show = case _ of
    Type str -> "Type " <> show str
    Class str -> "Class " <> show str
    Id str -> "Id " <> show str
    Universal -> "Universal"
    Attribute attr -> "Attribute " <> show attr
    Combinator combType sel ->
      "Combinator " <> show combType <> " " <> show sel

classSelector :: Parser String SelectorF
classSelector = do
  void $ string "."
  name <- identifier
  pure $ Class name

idSelector :: Parser String SelectorF
idSelector = do
  void $ string "#"
  name <- identifier
  pure $ Id name

typeSelector :: Parser String SelectorF
typeSelector = do
  name <- identifier
  pure $ Type name

universalSelector :: Parser String SelectorF
universalSelector = do
  void $ (string "*")
  pure Universal

attributeSelector :: Parser String SelectorF
attributeSelector = do
  void $ char '['
  name <- identifier
  op <- optionMaybe attributeOperator
  case op of
    Nothing -> do
      void $ char ']'
      pure $ Attribute $ AttributeExists name
    Just operator -> do
      value <- quotedString
      void $ char ']'
      pure $ Attribute $ makeAttributeSelector operator name value

basicSelector :: Parser String SelectorF
basicSelector = try classSelector
  <|> try idSelector
  <|> try universalSelector
  <|> try attributeSelector
  <|> typeSelector

selector :: Parser String (List SelectorF)
selector = do
  first <- basicSelector
  rest <- many do
    skipSpaces
    void $ optional
      ( choice
          [ try (char '>' *> pure unit)
          , try (char '+' *> pure unit)
          , try (char '~' *> pure unit)
          ]
      )
    skipSpaces
    basicSelector
  pure (first : rest)

flattenSelector :: Selector -> List SelectorF
flattenSelector (Selector sel) = case sel of
  Combinator _ (Selector n) -> sel : flattenSelector (Selector n)
  other -> pure other

selectors :: Parser String (List SelectorF)
selectors = do
  sels <- sepBy basicSelector (void $ many1 (char ' '))
  pure sels

type CSS = String

skipAtRule :: Parser String Unit
skipAtRule = do
  skipSpaces
  void $ char '@'
  void $ many (noneOf ['{'])
  void $ char '{'
  void $ manyTill skipNested (char '}')
  skipSpaces
  where
    skipNested = do
      void $ many (noneOf ['{', '}'])
      optional do
        void $ char '{'
        void $ manyTill (noneOf ['}']) (char '}')
      skipSpaces


stripDeclarationBlock :: Parser String String
stripDeclarationBlock = do
  skipSpaces
  optional skipAtRule
  sel <- many (noneOf [ '{' ])
  _ <- (string "{")
  _ <- manyTill (noneOf [ '}' ]) (char '}')
  skipSpaces
  pure $ fromCharArray (toUnfoldable sel :: Array Char)

stripAllDeclarationBlocks :: Parser String (List String)
stripAllDeclarationBlocks = do
  results <- many do
    try skipAtRule <|> pure unit
    try stripDeclarationBlock
  pure $ results

erasureDeclarationBlocks :: CSS -> Either ParseError (List String)
erasureDeclarationBlocks style = runParser style stripAllDeclarationBlocks

extractClassNames :: CSS -> Either ParseError (List SelectorF)
extractClassNames styles = do
  selectorStrs <- erasureDeclarationBlocks styles
  results <- traverse (\str -> runParser (trim str) selector) selectorStrs
  pure $ join results
