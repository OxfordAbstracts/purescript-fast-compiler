module TestMutualRecHoist where

import Prelude

-- Minimal reproduction: mutually recursive functions with dict args
-- The codegen should NOT hoist the cross-call as a var at init time

data Tree a = Leaf a | Branch (Tree a) (Tree a)

-- Two mutually recursive functions that process a tree
-- Each takes a Show constraint (dict arg)
processLeft :: forall a. Show a => Tree a -> String
processLeft (Leaf x) = show x
processLeft (Branch l r) = processRight l

processRight :: forall a. Show a => Tree a -> String
processRight (Leaf x) = show x
processRight (Branch l r) = processLeft r

-- TEST: "2"
test = processLeft (Branch (Branch (Leaf 1) (Leaf 2)) (Leaf 42))
