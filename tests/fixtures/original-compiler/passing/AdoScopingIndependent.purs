module Main where

import Prelude
import Effect.Console (log)

-- Tests that ado `<-` bindings don't shadow each other.
-- In ado, each `<-` expression is independent (applicative).
-- `let` bindings CAN see prior `<-` bindings.

data Maybe a = Nothing | Just a

instance functorMaybe :: Functor Maybe where
  map _ Nothing = Nothing
  map f (Just a) = Just (f a)

instance applyMaybe :: Apply Maybe where
  apply (Just f) (Just a) = Just (f a)
  apply _ _ = Nothing

-- x is a `<-` binding, y is a `let` that depends on x,
-- both should be available in `in`.
test :: Maybe Int
test = ado
  x <- Just 1
  let y = x + 1
  in x + y

-- Two `<-` bindings that rebind the same name as a local let.
-- The second `<-` expression should NOT see the first `<-` binding.
type Result = { a :: Int, b :: Int }

outerVal :: Int
outerVal = 42

testNoShadow :: Maybe Result
testNoShadow = ado
  x <- Just 1
  z <- Just outerVal  -- should see outerVal, not be affected by x binding
  in { a: x, b: z }

main = log "Done"
