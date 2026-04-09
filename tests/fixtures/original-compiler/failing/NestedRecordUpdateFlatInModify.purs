-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdateFlatInModify where

-- Reproduces the real-world bug where `context = { fields = "Not a record" }`
-- inside a record update is silently accepted.

type Inner = { fields :: { x :: Int, y :: String }, other :: Boolean }
type State = { context :: Inner, count :: Int }

mkState :: State
mkState = { context: { fields: { x: 1, y: "hello" }, other: true }, count: 0 }

-- This should fail: `context = { fields = "Not a record" }` sets context to
-- a record update section (function type), which can't unify with Inner.
modify :: State -> State
modify st =
  st
    { context = { fields = "Not a record" }
    }
