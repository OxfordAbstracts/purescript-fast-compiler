-- @shouldFailWith NoInstanceFound
module Main where

class Foo a b | a -> b

bar :: forall a. Foo Int a => Int -> Int
bar x = x

test :: Int
test = bar 0
