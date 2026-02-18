module LetAndWhere where

letSimple :: Int
letSimple = let x = 42 in x

letMultiple :: Int
letMultiple =
  let
    x = 1
    y = 2
  in x

whereSimple :: Int
whereSimple = result
  where
    result = 42

whereWithArgs :: Int -> Int
whereWithArgs n = double n
  where
    double x = x
