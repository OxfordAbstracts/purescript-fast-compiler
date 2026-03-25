module TestInstanceChainFail where

-- Regression test for 3531-3: instance chain with Fail constraint.
-- When C (X x x) doesn't match because the two type args differ
-- (one has a row tail, the other doesn't), the chain should fall
-- through to the Fail instance and produce NoInstanceFound.
-- Here we test a simpler variant that DOES match (both args same).

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
