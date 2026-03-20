module DeriveFunctor where

import Prelude (class Functor)

data Maybe a = Nothing | Just a

derive instance functorMaybe :: Functor Maybe

data Pair a = Pair a a

derive instance functorPair :: Functor Pair

data Tree a = Leaf | Branch (Tree a) a (Tree a)

derive instance functorTree :: Functor Tree
