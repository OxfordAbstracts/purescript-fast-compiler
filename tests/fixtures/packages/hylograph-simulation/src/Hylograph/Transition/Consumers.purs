-- | Tick Consumers
-- |
-- | Adapters that wrap various animation sources as TickConsumers
-- | for use with the Coordinator.
-- |
-- | Supported:
-- | - TransitionState from Engine.purs
-- | - TransitionGroup from Engine.purs
-- | - D3 force simulation (via ForceEngine)
-- |
-- | Documented (requires local FFI):
-- | - WASM force kernel (see pattern at bottom of file)
module Hylograph.Transition.Consumers
  ( -- * Transition consumers
    transitionConsumer
  , transitionGroupConsumer
    -- * Force simulation consumer
  , simulationConsumer
    -- * Re-exports for convenience
  , module Engine
  , module Coordinator
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Hylograph.Transition.Coordinator (TickResult(..), Milliseconds)
import Hylograph.Transition.Coordinator (TickResult(..), Milliseconds) as Coordinator
import Hylograph.Transition.Engine (TransitionState, TransitionGroup)
import Hylograph.Transition.Engine (start, tick, currentValue, isComplete, group, groupTick, groupValues, groupComplete) as Engine
import Hylograph.ForceEngine.Simulation (Simulation, tick) as FE

-- =============================================================================
-- Single Transition Consumer
-- =============================================================================

-- | Create a tick function for a single transition.
-- |
-- | Takes a Ref to the transition state and an effect to run on each tick
-- | with the current value. Returns Completed when the transition finishes.
-- |
-- | Usage:
-- | ```purescript
-- | stateRef <- Ref.new (Engine.start mySpec)
-- | let consumer = transitionConsumer stateRef \value -> setOpacity element value
-- | C.register coord { tick: consumer, onComplete: log "done" }
-- | ```
transitionConsumer
  :: forall a
   . Ref (TransitionState a)
  -> (a -> Effect Unit)          -- ^ Effect to run with current value
  -> Milliseconds
  -> Effect TickResult
transitionConsumer stateRef onValue deltaMs = do
  state <- Ref.read stateRef
  let newState = Engine.tick deltaMs state
  Ref.write newState stateRef
  onValue (Engine.currentValue newState)
  pure $ if Engine.isComplete newState
    then Completed
    else StillRunning

-- =============================================================================
-- Transition Group Consumer
-- =============================================================================

-- | Create a tick function for a group of coordinated transitions.
-- |
-- | Takes a Ref to the group and an effect to run on each tick with
-- | all current values. Returns Completed when all transitions finish.
-- |
-- | Usage:
-- | ```purescript
-- | groupRef <- Ref.new (Engine.group [spec1, spec2, spec3])
-- | let consumer = transitionGroupConsumer groupRef \[x, y, opacity] -> do
-- |       setPosition element x y
-- |       setOpacity element opacity
-- | C.register coord { tick: consumer, onComplete: log "all done" }
-- | ```
transitionGroupConsumer
  :: Ref TransitionGroup
  -> (Array Number -> Effect Unit)  -- ^ Effect to run with all current values
  -> Milliseconds
  -> Effect TickResult
transitionGroupConsumer groupRef onValues deltaMs = do
  grp <- Ref.read groupRef
  let newGroup = Engine.groupTick deltaMs grp
  Ref.write newGroup groupRef
  onValues (Engine.groupValues newGroup)
  pure $ if Engine.groupComplete newGroup
    then Completed
    else StillRunning

-- =============================================================================
-- D3 Force Simulation Consumer
-- =============================================================================

-- | Create a tick function for a D3 force simulation.
-- |
-- | The simulation's `tick` function is called on each frame.
-- | Returns Converged with the alpha value, or Completed when alpha drops below threshold.
-- |
-- | **Important**: Do NOT call `FE.start` on the simulation - the Coordinator
-- | owns the RAF loop. Just call `FE.create`, `FE.setNodes`, `FE.addForce`, etc.
-- |
-- | Usage:
-- | ```purescript
-- | sim <- FE.create FE.defaultConfig
-- | FE.setNodes myNodes sim
-- | FE.addForce (FE.ManyBody "charge" FE.defaultManyBody) sim
-- |
-- | C.register coord
-- |   { tick: simulationConsumer sim 0.001 \nodes -> renderNodes nodes
-- |   , onComplete: log "Simulation converged!"
-- |   }
-- | ```
simulationConsumer
  :: forall row linkRow
   . FE.Simulation row linkRow
  -> Number                           -- ^ Alpha threshold for completion (e.g., 0.001)
  -> (Effect Unit)                    -- ^ Effect to run after each tick (e.g., render)
  -> Milliseconds
  -> Effect TickResult
simulationConsumer sim alphaMin onTick _deltaMs = do
  alpha <- FE.tick sim
  onTick
  pure $ if alpha < alphaMin
    then Completed
    else Converged alpha

-- =============================================================================
-- WASM Simulation Consumer (Pattern)
-- =============================================================================

-- | The WASM force kernel has an identical tick model to D3:
-- |
-- | ```javascript
-- | // WASM API (from Rust via wasm-bindgen)
-- | simulation.tick()        // -> alpha: f32
-- | simulation.get_alpha()   // -> alpha: f32
-- | simulation.get_positions() // -> Float32Array
-- | simulation.is_running()  // -> bool
-- | ```
-- |
-- | A WASM consumer would look like:
-- |
-- | ```purescript
-- | wasmConsumer
-- |   :: WASMSimulation       -- ^ The WASM simulation instance
-- |   -> Number               -- ^ Alpha threshold for completion
-- |   -> (Effect Unit)        -- ^ Render callback
-- |   -> Milliseconds
-- |   -> Effect TickResult
-- | wasmConsumer sim alphaMin onTick _deltaMs = do
-- |   alpha <- wasmTick sim   -- FFI call to simulation.tick()
-- |   onTick
-- |   pure $ if alpha < alphaMin then Completed else Converged alpha
-- | ```
-- |
-- | Implementation note: The WASM kernel lives in showcases/wasm-force-demo/force-kernel.
-- | To use it, either:
-- | 1. Create the consumer in the showcase with local FFI bindings
-- | 2. Or move the WASM kernel into psd3-simulation as a reusable module
