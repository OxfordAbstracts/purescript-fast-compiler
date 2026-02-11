module Data.Huffman.Tree where

import Prelude
import Data.Array (foldl, insert, length, slice, sort)
import Data.Map.Internal (toUnfoldable)
import Data.Tuple (Tuple(..))
import Data.Huffman.Letter (Letter)
import Data.Huffman.Weights (Weights(..))

data HuffmanTree
  = Node (Array (HuffmanTree)) Number
  | Leaf Letter Number

instance eqHuffmanTree :: Eq HuffmanTree where
  eq (Node arr1 w1) (Node arr2 w2) = eq arr1 arr2 && eq w1 w2
  eq (Leaf s1 w1) (Leaf s2 w2) = eq s1 s2 && eq w1 w2
  eq _ _ = false

instance ordHuffmanTree :: Ord HuffmanTree where
  compare x y = compare (weight x) (weight y)

instance showHuffmanTree :: Show HuffmanTree where
  show (Node arr w) = show arr <> ": " <> show w
  show (Leaf s w) = show s <> ": " <> show w

weight :: HuffmanTree -> Number
weight (Node _ w) = w

weight (Leaf _ w) = w

sum :: Array HuffmanTree -> Number
sum arr = foldl (\acc x -> acc + weight x) 0.0 arr

fromWeights :: Weights -> HuffmanTree
fromWeights (Weights weights) = joinTree $ Node leaves 1.0
  where
  leaves = (\(Tuple k v) -> Leaf k v) <$> toUnfoldable weights

joinTree :: HuffmanTree -> HuffmanTree
joinTree (Leaf s w) = (Leaf s w)

joinTree (Node arr w)
  | length arr <= 2 = (Node arr w)
  | otherwise = joinTree (Node (insert (joinTree newNode) untouched) w)
    where
    pair = slice 0 2 (sort arr)

    untouched = slice 2 (length arr) (sort arr)

    newNode = Node pair (sum pair)
