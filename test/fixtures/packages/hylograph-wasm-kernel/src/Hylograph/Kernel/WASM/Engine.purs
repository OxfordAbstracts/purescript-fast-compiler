-- | WASM Engine Adapter
-- |
-- | High-performance force simulation using Rust/WebAssembly.
-- | Drop-in replacement for the D3.js-based simulation.
-- |
-- | Provides 3-4x speedup over D3.js for large graphs (10,000+ nodes)
-- | by offloading force calculations to compiled WebAssembly.
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Kernel.WASM.Engine as WASMEngine
-- | import Hylograph.Simulation.Core.Engine as Engine
-- |
-- | main = do
-- |   -- Initialize WASM module (once at app startup)
-- |   WASMEngine.initWasm "./pkg/force_kernel.js"
-- |
-- |   -- Create WASM simulation with nodes
-- |   wasmSim <- WASMEngine.create nodes links config
-- |
-- |   -- Create adapter for Scene Engine
-- |   let adapter = WASMEngine.mkAdapter wasmSim
-- |
-- |   -- Use with Scene Engine
-- |   engine <- Engine.createEngine adapter
-- | ```
module Hylograph.Kernel.WASM.Engine
  ( -- * Types
    WASMSim
  , WASMSimConfig
  , SimulationNode
  , defaultConfig
    -- * Initialization
  , initWasm
  , isWasmReady
    -- * Simulation Lifecycle
  , create
  , free
  , setNodes
  , setLinks
    -- * Engine Adapter
  , mkAdapter
    -- * Direct Operations
  , tick
  , tickN
  , getNodes
  , reheat
  , isRunning
    -- * Force Configuration
  , configureManyBody
  , configureLinks
  , configureCenter
  , enableForces
  ) where

import Prelude

import Data.Array (find)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Foreign.Object as Object
import Hylograph.Kernel.WASM.FFI as WASM
import Hylograph.Simulation.Core.Engine (EngineAdapter)
import Hylograph.Simulation.Core.Types (PositionMap, NodeRule)

-- =============================================================================
-- Types
-- =============================================================================

-- | Simulation node type for WASM engine.
-- | Contains both position data (synced with WASM) and user data.
type SimulationNode r =
  { id :: Int           -- Unique node identifier
  , x :: Number         -- Current x position
  , y :: Number         -- Current y position
  , vx :: Number        -- Velocity x (for D3 compatibility)
  , vy :: Number        -- Velocity y (for D3 compatibility)
  , fx :: Number        -- Fixed x position (NaN if not fixed)
  , fy :: Number        -- Fixed y position (NaN if not fixed)
  | r
  }

-- | WASM Simulation handle.
-- | Encapsulates the WASM simulation and PureScript node data.
type WASMSim r =
  { wasmSim :: WASM.WASMSimulation      -- WASM kernel handle
  , nodesRef :: Ref (Array (SimulationNode r))  -- PureScript node data
  , linksRef :: Ref (Array { source :: Int, target :: Int })  -- Link data
  }

-- | Configuration for creating a WASM simulation
type WASMSimConfig =
  { manyBody :: WASM.ManyBodyConfig
  , links :: WASM.LinkConfig
  , center :: WASM.CenterConfig
  , enableManyBody :: Boolean
  , enableLinks :: Boolean
  , enableCenter :: Boolean
  }

-- | Default simulation configuration
defaultConfig :: WASMSimConfig
defaultConfig =
  { manyBody:
      { strength: -30.0
      , theta: 0.9
      , distanceMin: 1.0
      , distanceMax: 10000.0
      }
  , links:
      { distance: 30.0
      , strength: 1.0
      , iterations: 1
      }
  , center:
      { x: 0.0
      , y: 0.0
      , strength: 1.0
      }
  , enableManyBody: true
  , enableLinks: true
  , enableCenter: true
  }

-- =============================================================================
-- Initialization
-- =============================================================================

-- | Initialize the WASM module. Call once at application startup.
initWasm :: String -> Aff Unit
initWasm = WASM.initWasm

-- | Check if WASM is initialized and ready
isWasmReady :: Effect Boolean
isWasmReady = WASM.isWasmReady

-- =============================================================================
-- Simulation Lifecycle
-- =============================================================================

-- | Create a new WASM simulation with nodes and links.
create
  :: forall r
   . Array (SimulationNode r)
  -> Array { source :: Int, target :: Int }
  -> WASMSimConfig
  -> Effect (WASMSim r)
create nodes links config = do
  -- Create WASM simulation
  wasmSim <- WASM.create (Array.length nodes)

  -- Configure forces
  WASM.configureManyBody wasmSim config.manyBody
  WASM.configureLinks wasmSim config.links
  WASM.configureCenter wasmSim config.center
  WASM.enableForces wasmSim
    { manyBody: config.enableManyBody
    , links: config.enableLinks
    , center: config.enableCenter
    }

  -- Set links
  WASM.setLinksFromRecords wasmSim links

  -- Sync initial positions to WASM
  WASM.syncPositionsToWasm wasmSim nodes

  -- Create refs
  nodesRef <- Ref.new nodes
  linksRef <- Ref.new links

  pure { wasmSim, nodesRef, linksRef }

-- | Free WASM simulation memory. Call when done with simulation.
free :: forall r. WASMSim r -> Effect Unit
free sim = WASM.free sim.wasmSim

-- | Set/replace all nodes in the simulation.
setNodes :: forall r. Array (SimulationNode r) -> WASMSim r -> Effect Unit
setNodes nodes sim = do
  -- Update node count in WASM
  WASM.setNodeCount sim.wasmSim (Array.length nodes)

  -- Sync positions to WASM
  WASM.syncPositionsToWasm sim.wasmSim nodes

  -- Update ref
  Ref.write nodes sim.nodesRef

-- | Set/replace all links in the simulation.
setLinks :: forall r. Array { source :: Int, target :: Int } -> WASMSim r -> Effect Unit
setLinks links sim = do
  WASM.setLinksFromRecords sim.wasmSim links
  Ref.write links sim.linksRef

-- =============================================================================
-- Engine Adapter
-- =============================================================================

-- | Create an EngineAdapter for use with the Scene Engine.
-- |
-- | This is the key integration point - allows WASMEngine to be used
-- | as a drop-in replacement for D3-based simulation in scene transitions.
mkAdapter
  :: forall r
   . WASMSim r
  -> EngineAdapter (SimulationNode r)
mkAdapter sim =
  { getNodes: getNodes sim
  , capturePositions: capturePositions
  , interpolatePositions: interpolatePositions sim
  , updatePositions: updatePositions sim
  , applyRulesInPlace: applyRulesInPlace sim
  , reinitializeForces: pure unit  -- WASM manages forces internally
  , reheat: reheat sim
  }

-- | Capture current positions from nodes as PositionMap
capturePositions :: forall r. Array (SimulationNode r) -> PositionMap
capturePositions nodes =
  Object.fromFoldable $ map (\n -> Tuple (show n.id) { x: n.x, y: n.y }) nodes

-- | Interpolate positions between start and target
interpolatePositions
  :: forall r
   . WASMSim r
  -> PositionMap
  -> PositionMap
  -> Number
  -> Effect Unit
interpolatePositions sim startPositions targetPositions progress = do
  nodes <- Ref.read sim.nodesRef
  let updatedNodes = map (interpolateNode startPositions targetPositions progress) nodes
  Ref.write updatedNodes sim.nodesRef
  -- Sync back to WASM
  WASM.syncPositionsToWasm sim.wasmSim updatedNodes

-- | Interpolate a single node
interpolateNode
  :: forall r
   . PositionMap
  -> PositionMap
  -> Number
  -> SimulationNode r
  -> SimulationNode r
interpolateNode startPositions targetPositions progress node =
  let key = show node.id
      newX = case Object.lookup key startPositions, Object.lookup key targetPositions of
        Just start, Just target -> start.x + (target.x - start.x) * progress
        _, Just target -> target.x
        Just start, _ -> start.x
        _, _ -> node.x
      newY = case Object.lookup key startPositions, Object.lookup key targetPositions of
        Just start, Just target -> start.y + (target.y - start.y) * progress
        _, Just target -> target.y
        Just start, _ -> start.y
        _, _ -> node.y
  in node { x = newX, y = newY }

-- | Set positions directly
updatePositions :: forall r. WASMSim r -> PositionMap -> Effect Unit
updatePositions sim positions = do
  nodes <- Ref.read sim.nodesRef
  let updatedNodes = map (updateNodePosition positions) nodes
  Ref.write updatedNodes sim.nodesRef
  WASM.syncPositionsToWasm sim.wasmSim updatedNodes

-- | Update a single node's position from PositionMap
updateNodePosition :: forall r. PositionMap -> SimulationNode r -> SimulationNode r
updateNodePosition positions node =
  case Object.lookup (show node.id) positions of
    Just pos -> node { x = pos.x, y = pos.y }
    Nothing -> node

-- | Apply rules to nodes in place
applyRulesInPlace
  :: forall r
   . WASMSim r
  -> Array (NodeRule (SimulationNode r))
  -> Effect Unit
applyRulesInPlace sim rules = do
  nodes <- Ref.read sim.nodesRef
  let updatedNodes = map (applyFirstMatchingRule rules) nodes
  Ref.write updatedNodes sim.nodesRef

  -- Sync fixed positions to WASM
  syncFixedNodes sim.wasmSim updatedNodes

-- | Apply the first matching rule to a node
applyFirstMatchingRule
  :: forall r
   . Array (NodeRule (SimulationNode r))
  -> SimulationNode r
  -> SimulationNode r
applyFirstMatchingRule rules node =
  case find (_.select >>> (_ $ node)) rules of
    Just rule -> rule.apply node
    Nothing -> node

-- | Sync fixed node positions (fx/fy) to WASM
syncFixedNodes :: forall r. WASM.WASMSimulation -> Array (SimulationNode r) -> Effect Unit
syncFixedNodes wasmSim nodes = do
  let indexed = Array.mapWithIndex Tuple nodes
  void $ traverse (syncFixedNode wasmSim) indexed
  where
  syncFixedNode wasm (Tuple idx node) =
    if isFinite node.fx && isFinite node.fy
      then WASM.fixNode wasm idx node.fx node.fy
      else WASM.unfixNode wasm idx

-- =============================================================================
-- Direct Operations
-- =============================================================================

-- | Run a single simulation tick
tick :: forall r. WASMSim r -> Effect Number
tick sim = do
  -- Run WASM tick
  alpha <- WASM.tick sim.wasmSim

  -- Sync positions back to PureScript
  nodes <- Ref.read sim.nodesRef
  updatedNodes <- WASM.syncPositionsFromWasm sim.wasmSim nodes
  Ref.write updatedNodes sim.nodesRef

  pure alpha

-- | Run multiple simulation ticks
tickN :: forall r. Int -> WASMSim r -> Effect Number
tickN n sim = do
  alpha <- WASM.tickN sim.wasmSim n

  -- Sync final positions back
  nodes <- Ref.read sim.nodesRef
  updatedNodes <- WASM.syncPositionsFromWasm sim.wasmSim nodes
  Ref.write updatedNodes sim.nodesRef

  pure alpha

-- | Get current nodes with positions
getNodes :: forall r. WASMSim r -> Effect (Array (SimulationNode r))
getNodes sim = do
  -- Get latest positions from WASM
  nodes <- Ref.read sim.nodesRef
  WASM.syncPositionsFromWasm sim.wasmSim nodes

-- | Reheat simulation (set alpha to 1.0)
reheat :: forall r. WASMSim r -> Effect Unit
reheat sim = WASM.reheat sim.wasmSim

-- | Check if simulation is still running
isRunning :: forall r. WASMSim r -> Effect Boolean
isRunning sim = WASM.isRunning sim.wasmSim

-- =============================================================================
-- Force Configuration
-- =============================================================================

-- | Configure many-body (charge) force
configureManyBody :: forall r. WASMSim r -> WASM.ManyBodyConfig -> Effect Unit
configureManyBody sim config = WASM.configureManyBody sim.wasmSim config

-- | Configure link (spring) force
configureLinks :: forall r. WASMSim r -> WASM.LinkConfig -> Effect Unit
configureLinks sim config = WASM.configureLinks sim.wasmSim config

-- | Configure center force
configureCenter :: forall r. WASMSim r -> WASM.CenterConfig -> Effect Unit
configureCenter sim config = WASM.configureCenter sim.wasmSim config

-- | Enable/disable forces individually
enableForces
  :: forall r
   . WASMSim r
  -> { manyBody :: Boolean, links :: Boolean, center :: Boolean }
  -> Effect Unit
enableForces sim = WASM.enableForces sim.wasmSim

-- =============================================================================
-- Helpers
-- =============================================================================

-- | Check if a number is finite (not NaN or Infinity)
foreign import isFinite :: Number -> Boolean
