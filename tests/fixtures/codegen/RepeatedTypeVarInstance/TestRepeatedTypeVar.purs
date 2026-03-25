module TestRepeatedTypeVar where

-- Regression test: repeated type variable in instance head (e.g., MyC (MyPair a a))
-- must check that both positions bind to the SAME type.
-- Previously, types_eq_lenient_with_unif treated Unif vars as wildcards,
-- so { foo :: Int | ?r } incorrectly matched { foo :: Int }, causing
-- instance chains to select the wrong instance.

class MyC x where
  myThing :: x -> x

data MyPair a b = MyPair

instance myCInstance :: MyC (MyPair a a) where
  myThing x = x

-- Both type args are the same: Int, Int → matches MyC (MyPair a a)
test1 :: MyPair Int Int
test1 = MyPair

test = myThing test1
-- TEST: {}
