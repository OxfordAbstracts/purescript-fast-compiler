module Elmish.TimeMachine.Types.Message
  ( Message(..)
  )
  where

-- | Initial states have no associated previous message, so it helps to have a
-- | type that wraps either an "initial state" message or the latest message
-- | which led to the current state
data Message msg
  = Message msg
  | Init
