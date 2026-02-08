module Bookhound.Utils.Char where

import Prelude

import Data.CodePoint.Unicode as CodePoint
import Data.String.CodePoints (codePointFromChar)

isDigit :: Char -> Boolean
isDigit = CodePoint.isDecDigit <<< codePointFromChar

isHexDigit :: Char -> Boolean
isHexDigit = CodePoint.isHexDigit <<< codePointFromChar

isLower :: Char -> Boolean
isLower = CodePoint.isAsciiLower <<< codePointFromChar

isUpper :: Char -> Boolean
isUpper = CodePoint.isAsciiUpper <<< codePointFromChar

isAlpha :: Char -> Boolean
isAlpha x = isLower x || isUpper x

isAlphaNum :: Char -> Boolean
isAlphaNum x = isAlpha x || isDigit x
