-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdateFlatMismatch where

-- Using `= { field = val }` syntax (flat update with record-update-section value)
-- should NOT be treated as a nested update `{ field { val } }`.
-- The value `{ fields = "Not a record" }` is a record update section,
-- not a nested record update, so it should fail to unify with the record field type.

type Inner = { x :: Int, y :: String }
type Outer = { inner :: Inner, name :: String }

outerVal :: Outer
outerVal = { inner: { x: 1, y: "hello" }, name: "test" }

-- This uses `=` syntax: `inner = { x = "wrong" }` means set `inner` to `{ x = "wrong" }`
-- which is a record update section `forall r. { x :: String | r } -> { x :: String | r }`,
-- NOT a nested update of `inner.x`. This should fail to typecheck.
bad :: Outer
bad = outerVal { inner = { x = "wrong" } }
