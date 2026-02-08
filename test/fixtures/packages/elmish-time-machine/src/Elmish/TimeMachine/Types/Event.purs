module Elmish.TimeMachine.Types.Event
  ( Event
  , IndexedEvent
  )
  where

import Data.Tuple.Nested (type (/\))
import Elmish.TimeMachine.Types.Message (Message)

-- | Represents a pairing of a given state with the message that led to it
type Event msg s = Message msg /\ s

-- | A record representing a given state, its corresponding message, along with
-- | its distance from the present (in "steps" where past events are negative
-- | integers and future events are positive)
type IndexedEvent msg s =
  { index :: Int
  , message :: Message msg
  , state :: s
  }
