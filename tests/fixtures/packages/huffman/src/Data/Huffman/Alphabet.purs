module Data.Huffman.Alphabet where

import Prelude
import Data.Set (Set, fromFoldable)
import Data.String (Pattern(..), split)
import Data.String.Unsafe (char)
import Data.Huffman.Letter (Letter(..))

newtype Alphabet
  = Alphabet (Set Letter)

instance eqAlphabet :: Eq Alphabet where
  eq (Alphabet x) (Alphabet y) = x == y

instance showAlphabet :: Show Alphabet where
  show (Alphabet set) = show set

fromString :: String -> Alphabet
fromString s = Alphabet (fromFoldable symbols)
  where
  symbols = Letter <<< char <$> split (Pattern "") s
