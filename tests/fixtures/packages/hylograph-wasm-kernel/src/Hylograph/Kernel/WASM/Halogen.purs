-- | Halogen Integration for WASM Force Simulations
-- |
-- | Provides subscription-based API for integrating WASM simulations with Halogen components.
-- | API-compatible with Hylograph.ForceEngine.Halogen for drop-in replacement.
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Kernel.WASM.Simulation as Sim
-- | import Hylograph.Kernel.WASM.Events (defaultCallbacks)
-- | import Hylograph.Kernel.WASM.Halogen (subscribeToSimulation)
-- |
-- | handleAction Initialize = do
-- |   callbacks <- liftEffect defaultCallbacks
-- |   sim <- liftEffect $ Sim.createWithCallbacks Sim.defaultConfig callbacks
-- |   emitter <- liftEffect $ subscribeToSimulation sim
-- |   void $ H.subscribe $ emitter <#> \event -> case event of
-- |     Tick -> UpdateNodePositions
-- |     Started -> SimStarted
-- |     Stopped -> SimStopped
-- |     AlphaDecayed alpha -> AlphaChanged alpha
-- | ```
module Hylograph.Kernel.WASM.Halogen
  ( subscribeToSimulation
  -- Re-export event types for convenience
  , module Events
  ) where

import Prelude

import Effect (Effect)
import Effect.Ref as Ref
import Halogen.Subscription as HS
import Hylograph.Kernel.WASM.Events (SimulationEvent(..), SimulationCallbacks) as Events
import Hylograph.Kernel.WASM.Events (SimulationEvent(..))
import Hylograph.Kernel.WASM.Simulation (Simulation, getCallbacks)
import Data.Maybe (Maybe(..))

-- | Create a Halogen subscription emitter for simulation events.
-- |
-- | This function wires up the simulation's callback system to emit
-- | Halogen-compatible events. The emitter can be used with `H.subscribe`.
-- |
-- | Note: The simulation must have been created with `createWithCallbacks`.
-- | If created with plain `create`, this function returns an emitter that
-- | never fires.
subscribeToSimulation :: forall row linkRow.
  Simulation row linkRow
  -> Effect (HS.Emitter SimulationEvent)
subscribeToSimulation sim = do
  { emitter, listener } <- HS.create

  -- Wire up callbacks to emit events
  case getCallbacks sim of
    Nothing -> pure unit  -- No callbacks configured, emitter will never fire
    Just cbs -> wireUpCallbacks listener cbs

  pure emitter

-- | Internal: Wire up simulation callbacks to emit events
wireUpCallbacks :: HS.Listener SimulationEvent -> Events.SimulationCallbacks -> Effect Unit
wireUpCallbacks listener cbs = do
  -- Wire tick callback
  Ref.write (HS.notify listener Tick) cbs.onTick

  -- Wire start callback
  Ref.write (HS.notify listener Started) cbs.onStart

  -- Wire stop callback
  Ref.write (HS.notify listener Stopped) cbs.onStop

  -- Wire alpha threshold callback
  Ref.write (\alpha -> HS.notify listener (AlphaDecayed alpha)) cbs.onAlphaThreshold
