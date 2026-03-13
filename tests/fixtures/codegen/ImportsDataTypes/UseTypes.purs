module UseTypes where

import Types (Color(..), Maybe(..))

isRed :: Color -> Boolean
isRed c = case c of
  Red -> true
  _ -> false

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def m = case m of
  Nothing -> def
  Just x -> x
