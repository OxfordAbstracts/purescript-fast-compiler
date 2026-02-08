module Elmish.TimeMachine.Types.History
  ( History
  , future
  , hasFuture
  , hasPast
  , init
  , jump
  , latestMessage
  , past
  , play
  , present
  , presentState
  , redo
  , stash
  , stop
  , track
  , undo
  )
  where

import Prelude

import Control.Monad.Rec.Class (Step(..), loop2, tailRec2)
import Data.Array as Array
import Data.List (List(..), (:))
import Data.List as List
import Data.Tuple (fst, snd)
import Data.Tuple.Nested ((/\))
import Elmish.TimeMachine.Types.Event (Event, IndexedEvent)
import Elmish.TimeMachine.Types.Message (Message(..))

-- | A zipper type that allows easy traversal through pairs of states and
-- | messages in an Elmish UI
newtype History msg s = History
  { past :: List (Event msg s)
  , present :: (Event msg s)
  , future :: List (Event msg s)
  }

-- Constructors

-- | Initializes the History type with a current state
init :: ∀ msg s. s -> History msg s
init s = History
  { past: Nil
  , present: Init /\ s
  , future: Nil
  }

-- Accessors

-- | Gets the current state paired with the latest message
present :: ∀ msg s. History msg s -> Event msg s
present (History h) = h.present

-- | Gets the current state
presentState :: ∀ msg s. History msg s -> s
presentState = snd <<< present

-- | Gets the latest message
latestMessage :: ∀ msg s. History msg s -> Message msg
latestMessage = fst <<< present

-- | Gets an array of the past state/message pairs, along with its index (or
-- | distance from the present), ordered chronologically
past :: ∀ msg s. History msg s -> Array (IndexedEvent msg s)
past (History h) = indexedEvents ((+) 1 >>> negate) h.past # Array.reverse

-- | Gets an array of the future state/message pairs, along with its index (or
-- | distance from the present), ordered chronologically
future :: ∀ msg s. History msg s -> Array (IndexedEvent msg s)
future (History h) = indexedEvents ((+) 1) h.future

-- | Returns true iff there is a nonempty past
hasPast :: ∀ msg s. History msg s -> Boolean
hasPast (History h) = not List.null h.past

-- | Returns true iff there is a nonempty future
hasFuture :: ∀ msg s. History msg s -> Boolean
hasFuture (History h) = not List.null h.future

indexedEvents :: ∀ msg s. (Int -> Int) -> List (Event msg s) -> Array (IndexedEvent msg s)
indexedEvents indexBy =
  Array.fromFoldable >>>
  Array.mapWithIndex \index (message /\ state) ->
    { index: indexBy index, message, state }

-- Controls

-- | Steps back one event into the past
-- | No-op if there is no past
undo :: ∀ msg s. History msg s -> History msg s
undo (History h) = case h.past of
  present' : past' ->
    History
      { past: past'
      , present: present'
      , future: h.present : h.future
      }
  Nil ->
    History h

-- | Steps forward one event into the future
-- | No-op if there is no future
redo :: ∀ msg s. History msg s -> History msg s
redo (History h) = case h.future of
  present' : future' ->
    History
      { past: h.present : h.past
      , present: present'
      , future: future'
      }
  Nil ->
    History h

-- | Adds a new event to the history, emptying out the future events
track :: ∀ msg s. History msg s -> msg -> s -> History msg s
track (History h) msg next = History
  { past: h.present : h.past
  , present: Message msg /\ next
  , future: Nil
  }

-- | For the case where the history is paused, stash changes in the future
stash :: ∀ msg s. History msg s -> msg -> s -> History msg s
stash (History h) msg next = History h
  { future = List.snoc h.future (Message msg /\ next) }

-- | Jumps the given distance, i.e. by a certain number of steps forward or
-- | backwards
jump :: ∀ msg s. Int -> History msg s -> History msg s
jump = tailRec2 go
  where
    go distance history
      | distance > 0
      , hasFuture history =
        loop2 (distance - 1) $ redo history
      | distance < 0
      , hasPast history =
        loop2 (distance + 1) $ undo history
      | otherwise =
        Done history

-- | Go to the end state of the history
play :: ∀ msg s. History msg s -> History msg s
play history
  | not hasFuture history = history
  | otherwise = play $ redo history

-- | Clears the future state, for when the stop button is pressed
stop :: ∀ msg s. History msg s -> History msg s
stop (History h) = History h
  { future = Nil }
