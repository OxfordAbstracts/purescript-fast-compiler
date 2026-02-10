-- | Tick Coordinator
-- |
-- | A unified animation coordinator that owns the RAF loop and routes ticks
-- | to multiple consumers (transitions, simulations, etc).
-- |
-- | Key concepts:
-- | - **Single RAF loop**: One coordinator per visualization, no competing frames
-- | - **TickConsumer**: Anything that needs ticks (transitions, simulations)
-- | - **Pull model**: Consumers compute on tick, coordinator reads results
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Transition.Coordinator as C
-- |
-- | main = do
-- |   coord <- C.create
-- |
-- |   -- Register a transition
-- |   transitionId <- C.register coord
-- |     { tick: \dt -> do
-- |         -- advance transition
-- |         pure C.StillRunning
-- |     , onComplete: log "done!"
-- |     }
-- |
-- |   -- Start the loop
-- |   C.start coord
-- | ```
module Hylograph.Transition.Coordinator
  ( -- * Coordinator
    Coordinator
  , create
  , start
  , stop
  , isRunning
    -- * Consumer registration
  , ConsumerId
  , TickResult(..)
  , Consumer
  , register
  , unregister
    -- * Utilities
  , Milliseconds
  ) where

import Prelude

import Data.Array (filter, null)
import Data.Foldable (for_)
import Data.Traversable (for)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Hylograph.Transition.RAF (AnimationFrameId, Timestamp, requestAnimationFrame, cancelAnimationFrame, performanceNow)

-- =============================================================================
-- Types
-- =============================================================================

-- | Time delta in milliseconds
type Milliseconds = Number

-- | Unique identifier for a registered consumer
newtype ConsumerId = ConsumerId Int

derive instance Eq ConsumerId

-- | Result of a tick - tells coordinator what to do next
data TickResult
  = StillRunning              -- ^ Keep sending ticks
  | Completed                 -- ^ Done, remove me from consumers
  | Converged Number          -- ^ Simulation-style: still running, here's alpha

-- | A tick consumer - anything that needs animation frames
type Consumer =
  { id :: ConsumerId
  , tick :: Milliseconds -> Effect TickResult
  , onComplete :: Effect Unit
  }

-- | Internal state of the coordinator
type CoordinatorState =
  { consumers :: Array Consumer
  , running :: Boolean
  , lastTimestamp :: Timestamp
  , nextId :: Int
  , frameId :: Maybe AnimationFrameId
  }

-- | The tick coordinator - owns the RAF loop
newtype Coordinator = Coordinator (Ref CoordinatorState)

-- =============================================================================
-- Creation
-- =============================================================================

-- | Create a new coordinator.
-- | The coordinator starts in stopped state - call `start` to begin.
create :: Effect Coordinator
create = do
  ref <- Ref.new
    { consumers: []
    , running: false
    , lastTimestamp: 0.0
    , nextId: 0
    , frameId: Nothing
    }
  pure $ Coordinator ref

-- =============================================================================
-- Consumer Registration
-- =============================================================================

-- | Register a consumer to receive ticks.
-- | Returns an ID that can be used to unregister later.
-- | If the coordinator is running, the consumer starts receiving ticks immediately.
register
  :: Coordinator
  -> { tick :: Milliseconds -> Effect TickResult, onComplete :: Effect Unit }
  -> Effect ConsumerId
register (Coordinator ref) spec = do
  state <- Ref.read ref
  let
    consumerId = ConsumerId state.nextId
    consumer = { id: consumerId, tick: spec.tick, onComplete: spec.onComplete }
  Ref.write (state { consumers = state.consumers <> [consumer], nextId = state.nextId + 1 }) ref
  pure consumerId

-- | Unregister a consumer. It will no longer receive ticks.
-- | If this was the last consumer, the loop continues but does nothing.
unregister :: Coordinator -> ConsumerId -> Effect Unit
unregister (Coordinator ref) consumerId = do
  Ref.modify_ (\s -> s { consumers = filter (\c -> c.id /= consumerId) s.consumers }) ref

-- =============================================================================
-- Loop Control
-- =============================================================================

-- | Start the animation loop.
-- | Does nothing if already running.
start :: Coordinator -> Effect Unit
start coord@(Coordinator ref) = do
  state <- Ref.read ref
  unless state.running do
    now <- performanceNow
    Ref.modify_ (_ { running = true, lastTimestamp = now }) ref
    scheduleFrame coord

-- | Stop the animation loop.
-- | Consumers remain registered but stop receiving ticks.
stop :: Coordinator -> Effect Unit
stop (Coordinator ref) = do
  state <- Ref.read ref
  when state.running do
    for_ state.frameId cancelAnimationFrame
    Ref.modify_ (_ { running = false, frameId = Nothing }) ref

-- | Check if the coordinator is currently running.
isRunning :: Coordinator -> Effect Boolean
isRunning (Coordinator ref) = do
  state <- Ref.read ref
  pure state.running

-- =============================================================================
-- Internal: Animation Loop
-- =============================================================================

-- | Schedule the next animation frame
scheduleFrame :: Coordinator -> Effect Unit
scheduleFrame coord@(Coordinator ref) = do
  frameId <- requestAnimationFrame (runFrame coord)
  Ref.modify_ (_ { frameId = Just frameId }) ref

-- | Run a single frame - tick all consumers, handle completions
runFrame :: Coordinator -> Timestamp -> Effect Unit
runFrame coord@(Coordinator ref) timestamp = do
  state <- Ref.read ref

  -- Only proceed if still running
  when state.running do
    let deltaMs = timestamp - state.lastTimestamp
    Ref.modify_ (_ { lastTimestamp = timestamp }) ref

    -- Tick all consumers and collect results
    results <- for state.consumers \consumer -> do
      result <- consumer.tick deltaMs
      pure { consumer, result }

    -- Handle completed consumers
    let completed = filter (\r -> isCompleted r.result) results
    for_ completed \r -> do
      r.consumer.onComplete
      unregister coord r.consumer.id

    -- Check if we should continue
    newState <- Ref.read ref
    if null newState.consumers
      then
        -- No consumers left, but keep running (consumers may be added later)
        scheduleFrame coord
      else
        -- Continue the loop
        scheduleFrame coord

-- | Check if a result indicates completion
isCompleted :: TickResult -> Boolean
isCompleted Completed = true
isCompleted _ = false
