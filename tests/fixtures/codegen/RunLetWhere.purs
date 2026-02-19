module RunLetWhere where

letSimple :: Int
letSimple = let x = 42 in x

whereSimple :: Int
whereSimple = result
  where
    result = 99
