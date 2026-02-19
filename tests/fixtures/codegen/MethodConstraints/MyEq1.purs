module MyEq1 where

import MyEq (class MyEq, myEq)

class MyEq1 f where
  myEq1 :: forall a. MyEq a => f a -> f a -> Boolean

instance myEq1Array :: MyEq1 Array where
  myEq1 = myEq
