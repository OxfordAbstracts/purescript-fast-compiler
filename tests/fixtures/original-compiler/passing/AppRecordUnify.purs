module Main where

-- Tests that App(f, a) can unify with Record types.
-- When f is a unif var, it should solve to Record.
apply :: forall f a. f a -> f a
apply x = x

test :: { x :: Int }
test = apply { x: 42 }
