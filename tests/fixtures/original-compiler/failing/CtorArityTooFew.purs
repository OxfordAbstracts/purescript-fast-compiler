-- @shouldFailWith IncorrectConstructorArity
module Main where

data Pair a b = Pair a b

test :: forall a b. Pair a b -> a
test (Pair x) = x
