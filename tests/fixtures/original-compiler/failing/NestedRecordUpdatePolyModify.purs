-- @shouldFailWith TypesDoNotUnify
module NestedRecordUpdatePolyModify where

import Prelude

-- Test that nested record updates catch type mismatches even when
-- the record type comes from a polymorphic function constraint.
-- The type annotation on `test` forces the lambda to be State -> State.

type Inner = { fields :: { x :: Int }, other :: Boolean }
type State = { context :: Inner, count :: Int, flag :: Boolean }

modify_ :: (State -> State) -> Unit
modify_ _ = unit

unit :: Unit
unit = modify_ (\x -> x)

test :: Unit
test = modify_ \st ->
  let
    newFlag = st.flag
  in
    st
      { flag = newFlag
      , context { fields = "Not a record" }
      }
