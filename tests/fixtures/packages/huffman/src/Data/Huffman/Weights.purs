module Data.Huffman.Weights where

import Prelude
import Data.Foldable (sum)
import Data.Int (toNumber)
import Data.Map (Map, values)
import Data.Huffman.Occurrences (Occurrences(..))
import Data.Huffman.Letter (Letter)

newtype Weights
  = Weights (Map Letter Number)

instance eqWeights :: Eq Weights where
  eq (Weights x) (Weights y) = eq x y

instance showWeights :: Show Weights where
  show (Weights x) = show x

fromOccurrences :: Occurrences -> Weights
fromOccurrences (Occurrences occ) = Weights $ normalize totalOccurrences <$> toNumber <$> occ
  where
  totalOccurrences = sum $ values occ

  normalize total x = (1.0 / toNumber total) * x
