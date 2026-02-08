-- | WASM Force Setup
-- |
-- | Declarative force configuration for WASM simulation engine.
-- | Uses the same Setup types as D3, providing functional parity.
-- |
-- | Key differences from D3:
-- | - WASM has fixed force types (one of each, not multiple named)
-- | - Dynamic (per-node) values use static fallback
-- | - Filters are not supported
-- |
-- | Example:
-- | ```purescript
-- | import Hylograph.ForceEngine.Setup (setup, manyBody, center, withStrength, static)
-- | import Hylograph.ForceEngine.Setup.WASM as WASM
-- |
-- | mySetup = setup "physics"
-- |   [ manyBody "charge" # withStrength (static (-30.0))
-- |   , center "center" # withX (static 0.0) # withY (static 0.0)
-- |   ]
-- |
-- | main = do
-- |   WASM.initWasm "./pkg/force_kernel.js"
-- |   sim <- WASM.create initialNodes initialLinks
-- |   result <- WASM.applySetupWithData mySetup newNodes newLinks sim
-- |   -- Use result.nodes.entered, result.nodes.exited for animations
-- | ```
module Hylograph.ForceEngine.Setup.WASM
  ( -- * Types
    WASMSim
  -- Note: SimulationNode is re-exported via 'module Exports' below

    -- * Initialization
  , initWasm
  , isWasmReady

    -- * Simulation Lifecycle
  , create
  , createEmpty
  , free

    -- * Apply Setup (the key functions - functional parity with D3)
  , applySetup
  , applySetupWithData

    -- * Direct Operations
  , tick
  , tickN
  , getNodes
  , getAlpha
  , reheat
  , isRunning

    -- * Re-exports from Setup (for convenience)
  , module Exports
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Foldable (for_)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Console (warn)
import Effect.Ref (Ref)
import Effect.Ref as Ref

import Hylograph.ForceEngine.WASM as FFI
import Hylograph.ForceEngine.Simulation (SimulationNode) as Exports
import Hylograph.ForceEngine.Simulation (SimulationNode)
import Hylograph.ForceEngine.Setup
  ( Setup
  , SetupParams
  , ForceConfig
  , ForceType(..)
  , Value(..)
  , GUPResult
  , GUPLinkResult
  , NodeGUPInternal
  , computeNodeGUP
  , computeLinkGUP
  , valueToNumber
  , getForces
  , getParams
  ) as Exports
import Hylograph.ForceEngine.Setup
  ( Setup
  , ForceConfig
  , ForceType(..)
  , Value(..)
  , GUPResult
  , GUPLinkResult
  , computeNodeGUP
  , computeLinkGUP
  , valueToNumber
  , getForces
  , getParams
  )

-- =============================================================================
-- Types
-- =============================================================================

-- | WASM Simulation handle.
-- | Wraps the low-level WASM handle with PureScript state management.
type WASMSim r =
  { wasmSim :: FFI.WASMSimulation
  , nodesRef :: Ref (Array (SimulationNode r))
  , linksRef :: Ref (Array { source :: Int, target :: Int })
  }

-- =============================================================================
-- Initialization
-- =============================================================================

-- | Initialize the WASM module. Call once at application startup.
initWasm :: String -> Aff Unit
initWasm = FFI.initWasm

-- | Check if WASM is initialized
isWasmReady :: Effect Boolean
isWasmReady = FFI.isWasmReady

-- =============================================================================
-- Simulation Lifecycle
-- =============================================================================

-- | Create a WASM simulation with initial nodes and links.
create
  :: forall r
   . Array (SimulationNode r)
  -> Array { source :: Int, target :: Int }
  -> Effect (WASMSim r)
create nodes links = do
  wasmSim <- FFI.create (Array.length nodes)

  -- Sync initial positions to WASM
  FFI.syncPositionsToWasm wasmSim nodes

  -- Set links
  FFI.setLinksFromRecords wasmSim links

  -- Create refs
  nodesRef <- Ref.new nodes
  linksRef <- Ref.new links

  pure { wasmSim, nodesRef, linksRef }

-- | Create an empty WASM simulation (for use with applySetupWithData)
createEmpty :: forall r. Effect (WASMSim r)
createEmpty = do
  wasmSim <- FFI.create 0
  nodesRef <- Ref.new []
  linksRef <- Ref.new []
  pure { wasmSim, nodesRef, linksRef }

-- | Free WASM simulation memory
free :: forall r. WASMSim r -> Effect Unit
free sim = FFI.free sim.wasmSim

-- =============================================================================
-- Apply Setup to WASM Simulation
-- =============================================================================

-- | Apply a Setup to a WASM simulation.
-- |
-- | Maps declarative force configuration to WASM kernel calls.
-- | This is idempotent - can be called repeatedly with different setups.
-- |
-- | Limitations vs D3:
-- | - Only one force of each type (first wins if multiple specified)
-- | - Dynamic values fall back to static (with warning)
-- | - Filters are ignored (with warning)
-- | - ForceRadial is not supported (warning logged)
applySetup
  :: forall r
   . Setup (SimulationNode r)
  -> WASMSim r
  -> Effect Unit
applySetup setupConfig sim = do
  -- Track which force types are enabled
  let forces = getForces setupConfig

  -- Find first force of each type
  let manyBodyForce = Array.find (\f -> f.forceType == ForceManyBody) forces
  let collideForce = Array.find (\f -> f.forceType == ForceCollide) forces
  let linkForce = Array.find (\f -> f.forceType == ForceLink) forces
  let centerForce = Array.find (\f -> f.forceType == ForceCenter) forces
  let posXForce = Array.find (\f -> f.forceType == ForcePositionX) forces
  let posYForce = Array.find (\f -> f.forceType == ForcePositionY) forces
  let radialForce = Array.find (\f -> f.forceType == ForceRadial) forces

  -- Warn about unsupported features
  for_ radialForce \_ ->
    warn "WASM Setup: ForceRadial is not supported by WASM kernel"

  -- Configure each force type
  for_ manyBodyForce (configureManyBody sim.wasmSim)
  for_ collideForce (configureCollide sim.wasmSim)
  for_ linkForce (configureLinks sim.wasmSim)
  for_ centerForce (configureCenter sim.wasmSim)
  for_ posXForce (configureForceX sim.wasmSim)
  for_ posYForce (configureForceY sim.wasmSim)

  -- Enable/disable forces based on what's in setup
  FFI.enableForces sim.wasmSim
    { manyBody: Array.any (\f -> f.forceType == ForceManyBody) forces
    , links: Array.any (\f -> f.forceType == ForceLink) forces
    , center: Array.any (\f -> f.forceType == ForceCenter) forces
    }

  -- Apply simulation params
  let params = getParams setupConfig
  FFI.setAlpha sim.wasmSim params.alpha
  FFI.setAlphaDecay sim.wasmSim params.alphaDecay
  FFI.setVelocityDecay sim.wasmSim params.velocityDecay

-- | Configure many-body force from ForceConfig
configureManyBody :: forall node. FFI.WASMSimulation -> ForceConfig node -> Effect Unit
configureManyBody wasmSim fc = do
  warnIfDynamic fc.strength "ManyBody strength"
  warnIfFiltered fc "ManyBody"
  FFI.configureManyBody wasmSim
    { strength: valueToNumber fc.strength
    , theta: fc.theta
    , distanceMin: fc.distanceMin
    , distanceMax: fc.distanceMax
    }

-- | Configure collide force from ForceConfig
-- | Note: Collide force support requires FFI additions to WASM module
configureCollide :: forall node. FFI.WASMSimulation -> ForceConfig node -> Effect Unit
configureCollide _wasmSim fc = do
  warnIfDynamic fc.radius "Collide radius"
  warnIfDynamic fc.strength "Collide strength"
  warn "WASM Setup: Collide force not yet implemented in FFI"

-- | Configure links force from ForceConfig
configureLinks :: forall node. FFI.WASMSimulation -> ForceConfig node -> Effect Unit
configureLinks wasmSim fc = do
  warnIfDynamic fc.distance "Link distance"
  warnIfDynamic fc.strength "Link strength"
  FFI.configureLinks wasmSim
    { distance: valueToNumber fc.distance
    , strength: valueToNumber fc.strength
    , iterations: fc.iterations
    }

-- | Configure center force from ForceConfig
configureCenter :: forall node. FFI.WASMSimulation -> ForceConfig node -> Effect Unit
configureCenter wasmSim fc = do
  warnIfDynamic fc.x "Center x"
  warnIfDynamic fc.y "Center y"
  warnIfDynamic fc.strength "Center strength"
  FFI.configureCenter wasmSim
    { x: valueToNumber fc.x
    , y: valueToNumber fc.y
    , strength: valueToNumber fc.strength
    }

-- | Configure forceX from ForceConfig
configureForceX :: forall node. FFI.WASMSimulation -> ForceConfig node -> Effect Unit
configureForceX _wasmSim fc = do
  warnIfDynamic fc.x "ForceX target"
  warnIfDynamic fc.strength "ForceX strength"
  -- Note: forceX/forceY would need FFI additions to WASM module
  pure unit

-- | Configure forceY from ForceConfig
configureForceY :: forall node. FFI.WASMSimulation -> ForceConfig node -> Effect Unit
configureForceY _wasmSim fc = do
  warnIfDynamic fc.y "ForceY target"
  warnIfDynamic fc.strength "ForceY strength"
  -- Note: forceX/forceY would need FFI additions to WASM module
  pure unit

-- | Warn if a value is dynamic (WASM doesn't support per-node values)
warnIfDynamic :: forall node a. Value node a -> String -> Effect Unit
warnIfDynamic (Dynamic _) name =
  warn $ "WASM Setup: " <> name <> " uses dynamic value, falling back to static"
warnIfDynamic (Static _) _ = pure unit

-- | Warn if a force has a filter (WASM doesn't support filters)
warnIfFiltered :: forall node. ForceConfig node -> String -> Effect Unit
warnIfFiltered fc name = case fc.filter of
  Just _ -> warn $ "WASM Setup: " <> name <> " filter is ignored by WASM kernel"
  Nothing -> pure unit

-- =============================================================================
-- Apply Setup with Data (GUP semantics)
-- =============================================================================

-- | Apply setup with new nodes and links, using GUP semantics.
-- |
-- | This provides functional parity with D3's applySetupWithData:
-- | 1. Force configuration (via applySetup)
-- | 2. Node GUP: diff desired vs current, preserve simulation state
-- | 3. Link GUP: diff desired vs current
-- |
-- | Simulation state preserved for updated nodes:
-- | - x, y: Current position
-- | - vx, vy: Current velocity
-- | - fx, fy: Pinned position
-- |
-- | Example:
-- | ```purescript
-- | result <- applySetupWithData mySetup newNodes newLinks sim
-- | animateEnter result.nodes.entered
-- | animateExit result.nodes.exited
-- | reheat sim
-- | ```
applySetupWithData
  :: forall r
   . Setup (SimulationNode r)
  -> Array (SimulationNode r)
  -> Array { source :: Int, target :: Int }
  -> WASMSim r
  -> Effect { nodes :: GUPResult (SimulationNode r), links :: GUPLinkResult () }
applySetupWithData setupConfig desiredNodes desiredLinks sim = do
  -- Get current state
  currentNodes <- Ref.read sim.nodesRef
  currentLinks <- Ref.read sim.linksRef

  -- Compute node GUP (reusing D3's logic)
  let nodeResult = computeNodeGUP currentNodes desiredNodes

  -- Write merged nodes to ref
  Ref.write nodeResult.merged sim.nodesRef

  -- Update WASM node count if changed
  let currentCount = Array.length currentNodes
  let newCount = Array.length nodeResult.merged
  when (currentCount /= newCount) do
    FFI.setNodeCount sim.wasmSim newCount

  -- Sync positions to WASM
  FFI.syncPositionsToWasm sim.wasmSim nodeResult.merged

  -- Compute link GUP
  let linkResult = computeLinkGUP currentLinks (toSimpleLinks desiredLinks)

  -- Write links to ref and WASM
  Ref.write desiredLinks sim.linksRef
  FFI.setLinksFromRecords sim.wasmSim desiredLinks

  -- Apply force configuration
  applySetup setupConfig sim

  -- Return GUP results for animation
  pure
    { nodes:
        { entered: nodeResult.entered
        , updated: nodeResult.updated
        , exited: nodeResult.exited
        }
    , links:
        { entered: linkResult.entered
        , updated: linkResult.updated
        , exited: linkResult.exited
        }
    }

-- | Convert links to simple source/target records for GUP computation
toSimpleLinks
  :: Array { source :: Int, target :: Int }
  -> Array { source :: Int, target :: Int }
toSimpleLinks = identity

-- =============================================================================
-- Direct Operations
-- =============================================================================

-- | Run a single simulation tick. Returns new alpha value.
tick :: forall r. WASMSim r -> Effect Number
tick sim = do
  alpha <- FFI.tick sim.wasmSim

  -- Sync positions back to PureScript
  nodes <- Ref.read sim.nodesRef
  updatedNodes <- FFI.syncPositionsFromWasm sim.wasmSim nodes
  Ref.write updatedNodes sim.nodesRef

  pure alpha

-- | Run multiple ticks. Returns final alpha.
tickN :: forall r. Int -> WASMSim r -> Effect Number
tickN n sim = do
  alpha <- FFI.tickN sim.wasmSim n

  -- Sync final positions back
  nodes <- Ref.read sim.nodesRef
  updatedNodes <- FFI.syncPositionsFromWasm sim.wasmSim nodes
  Ref.write updatedNodes sim.nodesRef

  pure alpha

-- | Get current nodes with positions
getNodes :: forall r. WASMSim r -> Effect (Array (SimulationNode r))
getNodes sim = do
  nodes <- Ref.read sim.nodesRef
  FFI.syncPositionsFromWasm sim.wasmSim nodes

-- | Get current alpha value
getAlpha :: forall r. WASMSim r -> Effect Number
getAlpha sim = FFI.getAlpha sim.wasmSim

-- | Reheat simulation (set alpha to 1.0)
reheat :: forall r. WASMSim r -> Effect Unit
reheat sim = FFI.reheat sim.wasmSim

-- | Check if simulation is still running
isRunning :: forall r. WASMSim r -> Effect Boolean
isRunning sim = FFI.isRunning sim.wasmSim
