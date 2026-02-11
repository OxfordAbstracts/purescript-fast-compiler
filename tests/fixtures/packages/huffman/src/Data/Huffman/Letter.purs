module Data.Huffman.Letter where

import Prim
import Prelude
import Data.String.CodeUnits (singleton)

newtype Letter
  = Letter Char

derive instance eqLetter :: Eq Letter
derive instance ordLetter :: Ord Letter

instance showLetter :: Show Letter where
  show (Letter x) = singleton x

toString :: Letter -> String
toString (Letter x) = singleton x
