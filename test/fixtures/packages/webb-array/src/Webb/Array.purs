module Webb.Array
  ( WArray
  , addAllFirst
  , addAllLast
  , addFirst
  , addLast
  , canFind
  , canFindEq
  , empty
  , findEq
  , first
  , isEmpty
  , module P
  , reject
  , size
  , dropWhileIncl, takeWhileIncl, dropWhileExcl, takeWhileExcl
  )
  where

import Prelude

import Data.Array as Array
import Data.Array as P
import Data.Foldable (class Foldable)
import Data.Maybe (Maybe, isJust)

{- All existing array functions that I find useful. -}

type WArray = Array

addLast :: forall a. a -> Array a -> Array a
addLast a = flip Array.snoc a 

addAllLast :: forall a f. Foldable f => f a -> Array a -> Array a
addAllLast items vec = vec <> (Array.fromFoldable items)

addFirst :: forall a. a -> Array a -> Array a
addFirst a = Array.cons a 

addAllFirst :: forall a f. Foldable f => f a -> Array a -> Array a
addAllFirst items vec = (Array.fromFoldable items) <> vec

first :: forall a. Array a -> Maybe a
first = Array.head

empty :: forall a. Array a
empty = []

isEmpty :: forall a. Array a -> Boolean
isEmpty = size >>> (_ <= 0)

size :: forall a. Array a -> Int
size = Array.length

canFind :: forall a. (a -> Boolean) -> Array a -> Boolean
canFind f vec = isJust (Array.find f vec)

findEq :: forall a. Eq a => a -> Array a -> Maybe a
findEq a vec = Array.find (_ == a) vec

canFindEq :: forall a. Eq a => a -> Array a -> Boolean
canFindEq a vec = isJust (findEq a vec)

reject :: forall a. (a -> Boolean) -> Array a -> Array a
reject f vec = Array.filter (not <<< f) vec

-- Drop while -- and then drop the item that didn't match.
dropWhileIncl :: forall a. (a -> Boolean) -> Array a -> Array a
dropWhileIncl f arr = let 
  rest = arr # Array.dropWhile f >>> Array.drop 1
  in rest
  
-- Take while -- and then take the item that didn't match as well.
takeWhileIncl :: forall a. (a -> Boolean) -> Array a -> Array a
takeWhileIncl f arr = let
  taken = arr # Array.takeWhile f >>> Array.take 1
  in taken

-- Only drop the items that matched
dropWhileExcl :: forall a. (a -> Boolean) -> Array a -> Array a
dropWhileExcl = Array.dropWhile
  
-- Only take the items that matched
takeWhileExcl :: forall a. (a -> Boolean) -> Array a -> Array a
takeWhileExcl = Array.takeWhile
