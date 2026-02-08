-- | Halogen Integration for Force Simulations
-- |
-- | Provides subscription-based API for integrating simulations with Halogen components.
-- |
-- | ## Recommended: High-Level API with Unified Events
-- |
-- | ```purescript
-- | import Hylograph.Simulation (runSimulation, SimulationEvent(..))
-- | import Hylograph.ForceEngine.Halogen (toHalogenEmitter)
-- |
-- | handleAction Initialize = do
-- |   { handle, events } <- liftEffect $ runSimulation config
-- |   halogenEmitter <- liftEffect $ toHalogenEmitter events
-- |   void $ H.subscribe $ halogenEmitter <#> SimEvent
-- |
-- | handleAction (SimEvent event) = case event of
-- |   Tick { alpha } -> H.modify_ _ { alpha = alpha }
-- |   Completed -> liftEffect $ log "Done!"
-- |   _ -> pure unit
-- | ```
-- |
-- | ## Legacy: Low-Level D3 Kernel API
-- |
-- | For advanced use cases requiring direct D3 callback control:
-- |
-- | ```purescript
-- | handleAction Initialize = do
-- |   callbacks <- liftEffect defaultCallbacks
-- |   sim <- liftEffect $ createWithCallbacks config callbacks
-- |   emitter <- liftEffect $ subscribeToSimulation sim
-- |   void $ H.subscribe $ emitter <#> SimulationEvent
-- | ```
module Hylograph.ForceEngine.Halogen
  ( -- * High-Level API (recommended)
    toHalogenEmitter
  , module SimEmitterExport

    -- * Legacy D3 Kernel API (for advanced use)
  , subscribeToSimulation
  , subscribeToGroup
  , D3SimulationEvent(..)
  , D3SimulationCallbacks
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref as Ref
import Halogen.Subscription as HS
import Data.Maybe (Maybe(..))

-- High-level unified emitter (from Hylograph.Simulation)
import Hylograph.Simulation.Emitter as Emitter
import Hylograph.Simulation.Emitter (SimulationEmitter)
import Hylograph.Simulation.Emitter (SimulationEmitter) as SimEmitterExport
import Hylograph.Simulation (SimulationEvent) as HighLevel

-- Legacy D3 kernel events (renamed to avoid conflict)
import Hylograph.Kernel.D3.Events (SimulationEvent, SimulationCallbacks)
import Hylograph.Kernel.D3.Events (SimulationEvent(..)) as D3
import Hylograph.Kernel.D3.Simulation (Simulation, getCallbacks)
import Hylograph.Kernel.D3.SimulationGroup (SimulationGroup, getGroupCallbacks)

-- Re-export legacy types with prefixed names
type D3SimulationEvent = SimulationEvent
type D3SimulationCallbacks = SimulationCallbacks

-- =============================================================================
-- High-Level API (Recommended)
-- =============================================================================

-- | Convert a framework-agnostic SimulationEmitter to Halogen's Emitter.
-- |
-- | This is the recommended way to integrate simulations with Halogen.
-- | It works with both D3 and WASM engines using the same event model.
-- |
-- | ```purescript
-- | import Hylograph.Simulation (runSimulation, SimulationEvent(..))
-- | import Hylograph.ForceEngine.Halogen (toHalogenEmitter)
-- |
-- | handleAction Initialize = do
-- |   { handle, events } <- liftEffect $ runSimulation config
-- |   halogenEmitter <- liftEffect $ toHalogenEmitter events
-- |   void $ H.subscribe $ halogenEmitter <#> SimEvent
-- |
-- | handleAction (SimEvent event) = case event of
-- |   Tick { alpha, nodeCount } -> do
-- |     H.modify_ _ { alpha = alpha }
-- |   Completed -> do
-- |     liftEffect $ log "Simulation converged!"
-- |   Started -> pure unit
-- |   Stopped -> pure unit
-- | ```
toHalogenEmitter :: SimulationEmitter -> Effect (HS.Emitter HighLevel.SimulationEvent)
toHalogenEmitter simEmitter = do
  -- Create Halogen emitter/listener pair
  { emitter, listener } <- HS.create

  -- Subscribe to simulation events and forward to Halogen listener
  _ <- Emitter.subscribe simEmitter \event ->
    HS.notify listener event

  pure emitter

-- =============================================================================
-- Legacy D3 Kernel API (for advanced/backwards-compatible use)
-- =============================================================================

-- | Create a Halogen subscription emitter for simulation events.
-- |
-- | This function wires up the simulation's callback system to emit
-- | Halogen-compatible events. The emitter can be used with `H.subscribe`.
-- |
-- | Note: The simulation must have been created with `createWithCallbacks`.
-- | If created with plain `create`, this function returns an emitter that
-- | never fires.
-- |
-- | Example:
-- | ```purescript
-- | -- In Halogen component Initialize:
-- | callbacks <- liftEffect defaultCallbacks
-- | sim <- liftEffect $ createWithCallbacks config callbacks
-- | emitter <- liftEffect $ subscribeToSimulation sim
-- | void $ H.subscribe $ emitter <#> SimulationEvent
-- |
-- | -- In handleAction:
-- | handleAction (SimulationEvent event) = case event of
-- |   Tick -> liftEffect updateDOMPositions
-- |   Started -> H.modify_ _ { simRunning = true }
-- |   Stopped -> H.modify_ _ { simRunning = false }
-- |   AlphaDecayed alpha -> when (alpha < 0.1) doSomething
-- | ```
subscribeToSimulation :: forall row linkRow.
  Simulation row linkRow
  -> Effect (HS.Emitter D3SimulationEvent)
subscribeToSimulation sim = do
  { emitter, listener } <- HS.create

  -- Wire up callbacks to emit events
  case getCallbacks sim of
    Nothing -> pure unit  -- No callbacks configured, emitter will never fire
    Just cbs -> wireUpCallbacks listener cbs

  pure emitter

-- | Internal: Wire up simulation callbacks to emit events
wireUpCallbacks :: HS.Listener D3SimulationEvent -> D3SimulationCallbacks -> Effect Unit
wireUpCallbacks listener cbs = do
  -- Wire tick callback
  Ref.write (HS.notify listener D3.Tick) cbs.onTick

  -- Wire start callback
  Ref.write (HS.notify listener D3.Started) cbs.onStart

  -- Wire stop callback
  Ref.write (HS.notify listener D3.Stopped) cbs.onStop

  -- Wire alpha threshold callback
  Ref.write (\alpha -> HS.notify listener (D3.AlphaDecayed alpha)) cbs.onAlphaThreshold

-- | Create a Halogen subscription emitter for a simulation group.
-- |
-- | This provides a single subscription for multiple synchronized simulations.
-- | The group must have been created with `createGroupWithCallbacks`.
-- |
-- | Example:
-- | ```purescript
-- | callbacks <- liftEffect defaultCallbacks
-- | group <- liftEffect $ createGroupWithCallbacks 6 defaultConfig callbacks
-- | emitter <- liftEffect $ subscribeToGroup group
-- | void $ H.subscribe $ emitter <#> \event -> case event of
-- |   Tick -> UpdateAllGraphPositions
-- |   Started -> H.modify_ _ { simRunning = true }
-- |   Stopped -> H.modify_ _ { simRunning = false }
-- |   _ -> pure unit
-- | liftEffect $ startGroup group
-- | ```
subscribeToGroup :: forall row linkRow.
  SimulationGroup row linkRow
  -> Effect (HS.Emitter D3SimulationEvent)
subscribeToGroup group = do
  { emitter, listener } <- HS.create

  -- Wire up callbacks to emit events
  case getGroupCallbacks group of
    Nothing -> pure unit  -- No callbacks configured, emitter will never fire
    Just cbs -> wireUpCallbacks listener cbs

  pure emitter
