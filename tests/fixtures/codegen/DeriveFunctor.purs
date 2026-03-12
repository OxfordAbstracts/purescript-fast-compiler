module DeriveFunctor where

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

data Maybe a = Nothing | Just a

derive instance functorMaybe :: Functor Maybe

data Pair a = Pair a a

derive instance functorPair :: Functor Pair

data Tree a = Leaf | Branch (Tree a) a (Tree a)

derive instance functorTree :: Functor Tree
