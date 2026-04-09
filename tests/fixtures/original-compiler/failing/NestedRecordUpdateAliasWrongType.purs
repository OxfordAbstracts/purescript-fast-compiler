-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdateAliasWrongType where

-- Test nested record update with type aliases (like FormContext in the real code).
-- The type alias indirection may prevent the typechecker from catching the mismatch.

type FormFields f =
  ( name :: f String String
  , age :: f String Int
  )

type FormContext fields actions input action =
  { fields :: { | fields }
  , actions :: { | actions }
  , input :: input
  , formActions :: action
  }

type MyContext = FormContext (FormFields FieldState) (FormFields FieldAction) Input Action

type FieldState a b = { value :: a, result :: b }
type FieldAction a b = { handleChange :: a -> b }
type Input = { title :: String }
type Action = { submit :: Unit }

type State =
  { context :: MyContext
  , count :: Int
  }

mkState :: State
mkState =
  { context:
      { fields: { name: { value: "", result: "" }, age: { value: "", result: 0 } }
      , actions: { name: { handleChange: \x -> x }, age: { handleChange: \_ -> 0 } }
      , input: { title: "test" }
      , formActions: { submit: unit }
      }
  , count: 0
  }

-- Nested update: context.fields is set to "Not a record" (String),
-- but it should be { | FormFields FieldState }.
bad :: State -> State
bad st = st { context { fields = "Not a record" } }
