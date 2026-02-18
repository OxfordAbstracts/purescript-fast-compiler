module CaseExpressions where

data Either a b = Left a | Right b

fromEither :: forall a. Either a a -> a
fromEither e = case e of
  Left x -> x
  Right x -> x

multiCase :: Int -> Int -> Int
multiCase a b = case a, b of
  0, _ -> 0
  _, 0 -> 0
  _, _ -> 1
