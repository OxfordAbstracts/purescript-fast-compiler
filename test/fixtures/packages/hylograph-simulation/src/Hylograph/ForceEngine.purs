-- | Pure Force Engine
-- |
-- | A clean, debuggable force simulation engine.
-- | Uses D3's force calculation algorithms but manages the simulation ourselves.
-- |
-- | Key benefits over d3.forceSimulation:
-- | - Full control over when forces run
-- | - Predictable, debuggable behavior
-- | - Clean PureScript types
-- | - No hidden state or timers
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.ForceEngine as FE
-- |
-- | main = do
-- |   sim <- FE.create FE.defaultConfig
-- |   FE.setNodes myNodes sim
-- |   FE.addForce (FE.ManyBody "charge" FE.defaultManyBody) sim
-- |   FE.onTick (renderNodes sim) sim
-- |   FE.start sim
-- | ```
module Hylograph.ForceEngine
  ( -- * Re-exports from Types
    module Types
    -- * Re-exports from Simulation
  , module Simulation
    -- * Re-exports from Events
  , module Events
    -- * Re-exports from Registry
  , module Registry
    -- * Re-exports from Core (low-level)
  , module Core
    -- * Re-exports from Links
  , module Links
  ) where

-- Note: Halogen integration is in a separate package: psd3-simulation-halogen
-- Import Hylograph.ForceEngine.Halogen from that package for subscribeToSimulation

import Hylograph.ForceEngine.Types
  ( SimNode
  , SimLink
  , RawLink
  , SimulationState
  , defaultSimParams
  , ManyBodyConfig
  , CollideConfig
  , LinkConfig
  , CenterConfig
  , ForceXConfig
  , ForceYConfig
  , RadialConfig
  , ForceSpec(..)
  , forceName
  , defaultManyBody
  , defaultCollide
  , defaultLink
  , defaultCenter
  ) as Types

import Hylograph.ForceEngine.Simulation
  ( Simulation
  , SimConfig
  , defaultConfig
  , create
  , createWithCallbacks
  , setNodes
  , setLinks
  , addForce
  , removeForce
  , start
  , stop
  , tick
  , reheat
  , onTick
  , setCallbacks
  , getCallbacks
  , isRunning
  , getAlpha
  , getNodes
  , attachDrag
  , attachGroupDrag
  ) as Simulation

import Hylograph.ForceEngine.Events
  ( SimulationEvent(..)
  , SimulationCallbacks
  , defaultCallbacks
  , onSimulationTick
  , onSimulationStart
  , onSimulationStop
  , onAlphaDecay
  ) as Events

import Hylograph.ForceEngine.Core
  ( ForceHandle
  , createManyBody
  , createCollide
  , createLink
  , createCenter
  , createForceX
  , createForceY
  , createRadial
  , initializeNodes
  , initializeForce
  , initializeLinkForce
  , applyForce
  , applyForces
  , integratePositions
  , decayAlpha
  , simulationTick
  , logNodes
  ) as Core

import Hylograph.ForceEngine.Links
  ( swizzleLinks
  , swizzleLinksByIndex
  , filterLinksToSubset
  ) as Links

import Hylograph.ForceEngine.Registry
  ( AnySimulation
  , register
  , unregister
  , lookup
  , listSimulations
  , stopAll
  , clearRegistry
  , debugRegistry
  , unsafeFromAny
  ) as Registry
