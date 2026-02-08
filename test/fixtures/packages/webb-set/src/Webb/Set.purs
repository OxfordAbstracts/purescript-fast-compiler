module Webb.Set
( module P
, toArray, fromArray, reject
, WSet
) 
where

import Prelude

import Data.Set as P
import Data.Set as Set
import Data.Set (Set)

type WSet a = Set a

toArray :: forall k. Set k -> Array k
toArray = Set.toUnfoldable

fromArray :: forall k. Ord k => Array k -> Set k
fromArray = Set.fromFoldable

reject :: forall k. Ord k => (k -> Boolean) -> Set k -> Set k
reject f = Set.filter (f >>> not)