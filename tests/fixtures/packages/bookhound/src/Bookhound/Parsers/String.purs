module Bookhound.Parsers.String (anyString, word, digits, uppers, lowers, alphas, alphaNums, spaces, tabs, newLines, spacesOrTabs, spacing, blankLine, blankLines, betweenQuotes, betweenDoubleQuotes, betweenParens, betweenSquare, betweenCurly, betweenAngle, betweenSpacing, maybeBetweenQuotes, maybeBetweenDoubleQuotes, maybeBetweenParens, maybeBetweenSquare, maybeBetweenCurly, maybeBetweenAngle, maybeBetweenSpacing) where

import Prelude hiding (between)

import Bookhound.Parser (Parser)
import Bookhound.ParserCombinators (between, inverse, maybeBetween, maybeSurroundedBy, surroundedBy, (->>-), (|+), (|?), (||*), (||+))
import Bookhound.Parsers.Char (alpha, alphaNum, anyChar, closeAngle, closeCurly, closeParens, closeSquare, digit, doubleQuote, lower, newLine, openAngle, openCurly, openParens, openSquare, quote, space, spaceOrTab, tab, upper, whiteSpace)
import Data.Foldable (fold)

anyString :: Parser String
anyString = (||*) anyChar

word :: Parser String
word = (||+) $ inverse whiteSpace

digits :: Parser String
digits = (||+) digit

uppers :: Parser String
uppers = (||+) upper

lowers :: Parser String
lowers = (||+) lower

alphas :: Parser String
alphas = (||+) alpha

alphaNums :: Parser String
alphaNums = (||+) alphaNum

spaces :: Parser String
spaces = (||+) space

tabs :: Parser String
tabs = (||+) tab

newLines :: Parser String
newLines = (||+) newLine

spacesOrTabs :: Parser String
spacesOrTabs = (||+) spaceOrTab

spacing :: Parser String
spacing = (||+) whiteSpace

blankLine :: Parser String
blankLine = (|?) spacesOrTabs ->>- newLine

blankLines :: Parser String
blankLines = fold <$> (|+) blankLine

betweenQuotes :: forall b. Parser b -> Parser b
betweenQuotes = surroundedBy quote

betweenSpacing :: forall b. Parser b -> Parser b
betweenSpacing = surroundedBy spacing

betweenDoubleQuotes :: forall b. Parser b -> Parser b
betweenDoubleQuotes = surroundedBy doubleQuote

betweenParens :: forall b. Parser b -> Parser b
betweenParens = between openParens closeParens

betweenSquare :: forall b. Parser b -> Parser b
betweenSquare = between openSquare closeSquare

betweenCurly :: forall b. Parser b -> Parser b
betweenCurly = between openCurly closeCurly

betweenAngle :: forall b. Parser b -> Parser b
betweenAngle = between openAngle closeAngle

maybeBetweenQuotes :: forall b. Parser b -> Parser b
maybeBetweenQuotes = maybeSurroundedBy quote

maybeBetweenDoubleQuotes :: forall b. Parser b -> Parser b
maybeBetweenDoubleQuotes = maybeSurroundedBy doubleQuote

maybeBetweenSpacing :: forall b. Parser b -> Parser b
maybeBetweenSpacing = maybeSurroundedBy spacing

maybeBetweenParens :: forall b. Parser b -> Parser b
maybeBetweenParens = maybeBetween openParens closeParens

maybeBetweenSquare :: forall b. Parser b -> Parser b
maybeBetweenSquare = maybeBetween openSquare closeSquare

maybeBetweenCurly :: forall b. Parser b -> Parser b
maybeBetweenCurly = maybeBetween openCurly closeCurly

maybeBetweenAngle :: forall b. Parser b -> Parser b
maybeBetweenAngle = maybeBetween openAngle closeAngle
