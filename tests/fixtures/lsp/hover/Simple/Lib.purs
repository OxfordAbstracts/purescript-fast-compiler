-- | Utility functions and classes for Simple
module Simple.Lib where

import Prelude

-- | This is a class
class Cl a where
  member :: a -> a

data LibT
  = LibA
  | LibB

times2 n = n * 2

-- | Adds one to a number
foreign import addOne :: Int -> Int

-- | Opaque effect type
foreign import data Effect :: Type -> Type

-- | Custom functor
class MyFunctor f where 
  myMap :: forall a b. (a -> b) -> f a -> f b
 