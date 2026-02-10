module Bookhound.Utils.Array where

import Prelude

import Data.Array (length, mapMaybe)
import Data.Array as Array
import Data.Char (fromCharCode, toCharCode)

hasNone :: forall a. Array a -> Boolean
hasNone xs = length xs == zero

hasSome :: forall a. Array a -> Boolean
hasSome xs = length xs > zero

hasMultiple :: forall a. Array a -> Boolean
hasMultiple xs = length xs > one

infixr 8 range as ..

class Range a where
  range :: a -> a -> Array a

instance Range Char where
  range c1 c2 =
    mapMaybe fromCharCode $ range (toCharCode c1) (toCharCode c2)

instance Range Int where
  range = Array.range
