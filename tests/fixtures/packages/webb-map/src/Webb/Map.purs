module Webb.Map 
( module P
, WMap
, initOrUpdate, toArray, valuesArray, keysArray
, fromArray
)
where

import Prelude

import Control.Alt ((<|>))
import Data.Map as Map
import Data.Map as P
import Data.Tuple (Tuple)
import Webb.Array as Array

type WMap = Map.Map

-- Update a key or set a default value.
initOrUpdate :: forall k v. Ord k => k -> v -> (v -> v) -> WMap k v -> WMap k v
initOrUpdate k default f map = Map.alter alter k map
  where
  alter mvalue = updated mvalue <|> pure default
  updated mvalue = f <$> mvalue
  
toArray :: forall k v. WMap k v -> Array (Tuple k v)
toArray = Map.toUnfoldable

fromArray :: forall k v. Ord k => Array (Tuple k v) -> WMap k v
fromArray = Map.fromFoldable
  
valuesArray :: forall k v. WMap k v -> Array v
valuesArray map = map # Map.values >>> Array.fromFoldable

keysArray :: forall k v. WMap k v -> Array k
keysArray map = map # Map.keys >>> Array.fromFoldable