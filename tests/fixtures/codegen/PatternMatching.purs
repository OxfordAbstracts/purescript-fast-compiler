module PatternMatching where

data Maybe a = Nothing | Just a
data Color = Red | Green | Blue

wildcardMatch :: Int -> Int
wildcardMatch _ = 0

varMatch :: Int -> Int
varMatch x = x

literalMatch :: Int -> String
literalMatch n = case n of
  0 -> "zero"
  1 -> "one"
  _ -> "other"

boolMatch :: Boolean -> String
boolMatch b = case b of
  true -> "yes"
  false -> "no"

constructorMatch :: Maybe Int -> Int
constructorMatch m = case m of
  Nothing -> 0
  Just x -> x

nestedMatch :: Maybe (Maybe Int) -> Int
nestedMatch m = case m of
  Nothing -> 0
  Just Nothing -> 1
  Just (Just x) -> x

colorToInt :: Color -> Int
colorToInt c = case c of
  Red -> 0
  Green -> 1
  Blue -> 2

asPattern :: Maybe Int -> Maybe Int
asPattern m = case m of
  j@(Just _) -> j
  Nothing -> Nothing
