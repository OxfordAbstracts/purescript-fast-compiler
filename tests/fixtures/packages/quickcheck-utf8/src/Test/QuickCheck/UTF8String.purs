module Test.QuickCheck.UTF8String where

import Prelude
import Data.Enum (toEnumWithDefaults)
import Data.String.CodeUnits (fromCharArray)
import Control.Alternative ((<|>))
import Test.QuickCheck.Gen (Gen, chooseInt, arrayOf)


genChar :: Gen Char
genChar = toEnumWithDefaults bottom top <$> withoutControlSeq
  where
    withoutControlSeq = chooseInt 0 (0xD800 - 1) <|> chooseInt (0xDFFF + 1) 65536

genString :: Gen String
genString = fromCharArray <$> arrayOf genChar
