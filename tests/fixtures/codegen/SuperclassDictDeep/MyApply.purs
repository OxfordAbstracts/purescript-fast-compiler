module MyApply where

import MyFunctor (class MyFunctor)

class MyFunctor f <= MyApply f where
  myApply :: forall a b. f (a -> b) -> f a -> f b

infixl 4 myApply as <*>
