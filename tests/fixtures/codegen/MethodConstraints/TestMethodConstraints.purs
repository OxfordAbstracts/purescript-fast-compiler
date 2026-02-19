module TestMethodConstraints where

import MyEq (class MyEq)
import MyEq1 (class MyEq1, myEq1)

-- Use eq1 in a constrained function to verify dict passing works
testEq1 :: forall a. MyEq a => Array a -> Array a -> Boolean
testEq1 xs ys = myEq1 xs ys
