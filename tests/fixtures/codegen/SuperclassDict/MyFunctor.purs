module MyFunctor where

class MyFunctor f where
  myMap :: forall a b. (a -> b) -> f a -> f b
