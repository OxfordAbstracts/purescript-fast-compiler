-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdateTypeMismatch where

type Inner = { x :: Int, y :: String }
type Outer = { inner :: Inner, name :: String }

outerVal :: Outer
outerVal = { inner: { x: 1, y: "hello" }, name: "test" }

-- Nested update with wrong type: x is Int but we give it a String
bad :: Outer
bad = outerVal { inner { x = "not an int" } }
