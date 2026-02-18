module DataConstructors where

data Color = Red | Green | Blue

data Maybe a = Nothing | Just a

data Pair a b = Pair a b

data Tree a = Leaf a | Branch (Tree a) (Tree a)

nullaryUse :: Color
nullaryUse = Red

unaryUse :: Maybe Int
unaryUse = Just 42

nothingUse :: Maybe Int
nothingUse = Nothing

pairUse :: Pair Int String
pairUse = Pair 1 "hello"
