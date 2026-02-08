module Bookhound.Parsers.Char (module AnyChar, digit, hexDigit, upper, lower, alpha, alphaNum, space, tab, newLine, spaceOrTab, whiteSpace, comma, dot, colon, quote, doubleQuote, dash, plus, equal, underscore, hashTag, question, openParens, closeParens, openSquare, closeSquare, openCurly, closeCurly, openAngle, closeAngle) where

import Prelude

import Bookhound.Parser (Parser, anyChar)
import Bookhound.Parser as Parser
import Bookhound.Parser (anyChar) as AnyChar
import Bookhound.ParserCombinators (is)
import Bookhound.Utils.Char (isAlpha, isAlphaNum, isDigit, isHexDigit, isLower, isUpper)
import Control.Alt ((<|>))

digit :: Parser Char
digit = satisfy isDigit

hexDigit :: Parser Char
hexDigit = satisfy isHexDigit

upper :: Parser Char
upper = satisfy isUpper

lower :: Parser Char
lower = satisfy isLower

alpha :: Parser Char
alpha = satisfy isAlpha

alphaNum :: Parser Char
alphaNum = satisfy isAlphaNum

space :: Parser Char
space = is ' '

tab :: Parser Char
tab = is '\t'

newLine :: Parser Char
newLine = is '\n'

spaceOrTab :: Parser Char
spaceOrTab = space <|> tab

whiteSpace :: Parser Char
whiteSpace = spaceOrTab <|> newLine

comma :: Parser Char
comma = is ','

dot :: Parser Char
dot = is '.'

colon :: Parser Char
colon = is ':'

quote :: Parser Char
quote = is '\''

doubleQuote :: Parser Char
doubleQuote = is '"'

dash :: Parser Char
dash = is '-'

plus :: Parser Char
plus = is '+'

equal :: Parser Char
equal = is '='

underscore :: Parser Char
underscore = is '_'

hashTag :: Parser Char
hashTag = is '#'

question :: Parser Char
question = is '?'

openParens :: Parser Char
openParens = is '('

closeParens :: Parser Char
closeParens = is ')'

openSquare :: Parser Char
openSquare = is '['

closeSquare :: Parser Char
closeSquare = is ']'

openCurly :: Parser Char
openCurly = is '{'

closeCurly :: Parser Char
closeCurly = is '}'

openAngle :: Parser Char
openAngle = is '<'

closeAngle :: Parser Char
closeAngle = is '>'

satisfy :: (Char -> Boolean) -> Parser Char
satisfy = flip Parser.satisfy anyChar
