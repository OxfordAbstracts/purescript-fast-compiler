-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdateFlatVsNested where

-- This tests that `rec { a = { b = val } }` (flat update, using `=`)
-- is NOT silently reinterpreted as `rec { a { b = val } }` (nested update).
--
-- With flat update semantics: `a` is set to `{ b = val }` (a record update section).
--   Type: `a :: { b :: Int | r } -> { b :: Int | r }`, which is a function, not a record.
--   This should fail since `a :: { b :: Int }`.
--
-- With (incorrect) nested update semantics: `a.b` is updated to `val`.
--   This would succeed since `b :: Int` and `val :: Int`.

type Inner = { b :: Int }
type Outer = { a :: Inner }

outerVal :: Outer
outerVal = { a: { b: 1 } }

-- BUG: This should fail because `= { b = 42 }` means "set a to the value { b = 42 }"
-- (a record update section), NOT "nested update a.b to 42".
-- But the compiler currently treats it as a nested update and accepts it.
bad :: Outer
bad = outerVal { a = { b = 42 } }
