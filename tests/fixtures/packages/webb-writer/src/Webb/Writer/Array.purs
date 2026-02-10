module Webb.Writer.Array where

import Prelude

import Data.Array as A


dropWhileIncl :: forall a. (a -> Boolean) -> Array a -> Array a
dropWhileIncl f arr = let 
  rest = arr # A.dropWhile f >>> A.drop 1
  in rest
  
takeWhileIncl :: forall a. (a -> Boolean) -> Array a -> Array a
takeWhileIncl f arr = let
  taken = arr # A.takeWhile f >>> A.take 1
  in taken

dropWhileExcl :: forall a. (a -> Boolean) -> Array a -> Array a
dropWhileExcl = A.dropWhile
  
takeWhileExcl :: forall a. (a -> Boolean) -> Array a -> Array a
takeWhileExcl = A.takeWhile
