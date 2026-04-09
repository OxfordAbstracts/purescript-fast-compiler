-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdateWrongValueType where

-- Nested record update where the value has the wrong type.
-- `context { fields = "Not a record" }` should fail because
-- context.fields :: { x :: Int } but "Not a record" :: String.

type Inner = { fields :: { x :: Int }, other :: Boolean }
type Outer = { context :: Inner, name :: String }

outerVal :: Outer
outerVal = { context: { fields: { x: 1 }, other: true }, name: "test" }

bad :: Outer
bad = outerVal { context { fields = "Not a record" } }
