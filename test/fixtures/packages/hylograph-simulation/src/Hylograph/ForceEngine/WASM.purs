-- | WASM Force Engine
-- |
-- | High-performance force simulation using Rust/WebAssembly.
-- | Provides 3-4x speedup over D3.js for large graphs (10,000+ nodes).
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.ForceEngine.WASM as WASM
-- |
-- | main = do
-- |   -- Initialize WASM module (once at app startup)
-- |   WASM.initWasm "./pkg/force_kernel.js"
-- |
-- |   -- Create simulation
-- |   sim <- WASM.create 1000
-- |
-- |   -- Configure forces
-- |   WASM.configureManyBody sim { strength: -30.0, theta: 0.9, distanceMin: 1.0, distanceMax: 10000.0 }
-- |   WASM.configureLinks sim { distance: 30.0, strength: 1.0, iterations: 1 }
-- |   WASM.configureCenter sim { x: 0.0, y: 0.0, strength: 1.0 }
-- |
-- |   -- Set links
-- |   WASM.setLinks sim [0, 1, 1, 2, 2, 3]  -- [source, target, source, target, ...]
-- |
-- |   -- Run simulation
-- |   WASM.tick sim
-- |
-- |   -- Get results
-- |   positions <- WASM.getPositions sim  -- [x0, y0, x1, y1, ...]
-- | ```
module Hylograph.ForceEngine.WASM
  ( -- * Types
    WASMSimulation
  , ManyBodyConfig
  , LinkConfig
  , CenterConfig
    -- * Initialization
  , initWasm
  , isWasmReady
    -- * Simulation Lifecycle
  , create
  , free
  , setNodeCount
    -- * Node Operations
  , setPosition
  , setAllPositions
  , getPositions
  , getPositionsAsObjects
  , fixNode
  , unfixNode
    -- * Link Operations
  , setLinks
  , setLinksFromRecords
    -- * Force Configuration
  , configureManyBody
  , configureLinks
  , configureCenter
  , enableForces
    -- * Simulation Control
  , setAlpha
  , getAlpha
  , setAlphaDecay
  , setVelocityDecay
  , reheat
  , tick
  , tickN
  , isRunning
    -- * Queries
  , nodeCount
  , linkCount
    -- * Node Array Sync
  , syncPositionsToWasm
  , syncPositionsFromWasm
  ) where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)


-- =============================================================================
-- Types
-- =============================================================================

-- | Opaque type for WASM simulation handle
foreign import data WASMSimulation :: Type

-- | Many-body force configuration
type ManyBodyConfig =
  { strength :: Number     -- Positive = attract, negative = repel (default: -30)
  , theta :: Number        -- Barnes-Hut approximation parameter (default: 0.9)
  , distanceMin :: Number  -- Minimum distance (default: 1.0)
  , distanceMax :: Number  -- Maximum distance (default: Infinity)
  }

-- | Link force configuration
type LinkConfig =
  { distance :: Number     -- Target distance (default: 30)
  , strength :: Number     -- Spring strength 0-1 (default: 1.0)
  , iterations :: Int      -- Iterations per tick (default: 1)
  }

-- | Center force configuration
type CenterConfig =
  { x :: Number            -- Center x (default: 0)
  , y :: Number            -- Center y (default: 0)
  , strength :: Number     -- Strength (default: 1.0)
  }


-- =============================================================================
-- FFI Declarations
-- =============================================================================

foreign import initWasm_ :: String -> EffectFnAff Unit
foreign import isWasmReady_ :: Effect Boolean
foreign import createSimulation_ :: Int -> Effect WASMSimulation
foreign import freeSimulation_ :: WASMSimulation -> Effect Unit
foreign import setNodeCount_ :: WASMSimulation -> Int -> Effect Unit
foreign import setLinks_ :: WASMSimulation -> Array Int -> Effect Unit
foreign import setPosition_ :: WASMSimulation -> Int -> Number -> Number -> Effect Unit
foreign import setAllPositions_ :: WASMSimulation -> Array Number -> Effect Unit
foreign import getPositions_ :: WASMSimulation -> Effect (Array Number)
foreign import getPositionsAsObjects_ :: WASMSimulation -> Effect (Array { x :: Number, y :: Number })
foreign import fixNode_ :: WASMSimulation -> Int -> Number -> Number -> Effect Unit
foreign import unfixNode_ :: WASMSimulation -> Int -> Effect Unit
foreign import configureManyBody_ :: WASMSimulation -> ManyBodyConfig -> Effect Unit
foreign import configureLinks_ :: WASMSimulation -> LinkConfig -> Effect Unit
foreign import configureCenter_ :: WASMSimulation -> CenterConfig -> Effect Unit
foreign import enableForces_ :: WASMSimulation -> Boolean -> Boolean -> Boolean -> Effect Unit
foreign import setAlpha_ :: WASMSimulation -> Number -> Effect Unit
foreign import getAlpha_ :: WASMSimulation -> Effect Number
foreign import setAlphaDecay_ :: WASMSimulation -> Number -> Effect Unit
foreign import setVelocityDecay_ :: WASMSimulation -> Number -> Effect Unit
foreign import reheat_ :: WASMSimulation -> Effect Unit
foreign import tick_ :: WASMSimulation -> Effect Number
foreign import tickN_ :: WASMSimulation -> Int -> Effect Number
foreign import isRunning_ :: WASMSimulation -> Effect Boolean
foreign import nodeCount_ :: WASMSimulation -> Effect Int
foreign import linkCount_ :: WASMSimulation -> Effect Int
foreign import syncPositionsToWasm_ :: forall r. WASMSimulation -> Array { x :: Number, y :: Number | r } -> Effect Unit
foreign import syncPositionsFromWasm_ :: forall r. WASMSimulation -> Array { x :: Number, y :: Number, vx :: Number, vy :: Number | r } -> Effect (Array { x :: Number, y :: Number, vx :: Number, vy :: Number | r })


-- =============================================================================
-- Initialization
-- =============================================================================

-- | Initialize the WASM module. Call once at application startup.
-- |
-- | The URL should point to the generated JavaScript module from wasm-pack.
-- | Example: `initWasm "./pkg/force_kernel.js"`
initWasm :: String -> Aff Unit
initWasm url = fromEffectFnAff (initWasm_ url)

-- | Check if WASM is initialized and ready
isWasmReady :: Effect Boolean
isWasmReady = isWasmReady_


-- =============================================================================
-- Simulation Lifecycle
-- =============================================================================

-- | Create a new WASM simulation with the given number of nodes.
-- | Nodes are initialized in a phyllotaxis (sunflower) pattern.
create :: Int -> Effect WASMSimulation
create = createSimulation_

-- | Free WASM simulation memory. Call when done with simulation.
free :: WASMSimulation -> Effect Unit
free = freeSimulation_

-- | Resize simulation to new node count
setNodeCount :: WASMSimulation -> Int -> Effect Unit
setNodeCount = setNodeCount_


-- =============================================================================
-- Node Operations
-- =============================================================================

-- | Set a single node's position
setPosition :: WASMSimulation -> Int -> Number -> Number -> Effect Unit
setPosition = setPosition_

-- | Set all positions from flat array [x0, y0, x1, y1, ...]
setAllPositions :: WASMSimulation -> Array Number -> Effect Unit
setAllPositions = setAllPositions_

-- | Get all positions as flat array [x0, y0, x1, y1, ...]
getPositions :: WASMSimulation -> Effect (Array Number)
getPositions = getPositions_

-- | Get positions as array of {x, y} objects
getPositionsAsObjects :: WASMSimulation -> Effect (Array { x :: Number, y :: Number })
getPositionsAsObjects = getPositionsAsObjects_

-- | Fix a node at a position (like D3's fx/fy)
fixNode :: WASMSimulation -> Int -> Number -> Number -> Effect Unit
fixNode = fixNode_

-- | Unfix a node
unfixNode :: WASMSimulation -> Int -> Effect Unit
unfixNode = unfixNode_


-- =============================================================================
-- Link Operations
-- =============================================================================

-- | Set links from flat array [source0, target0, source1, target1, ...]
setLinks :: WASMSimulation -> Array Int -> Effect Unit
setLinks = setLinks_

-- | Set links from array of records with source/target fields
setLinksFromRecords :: forall r. WASMSimulation -> Array { source :: Int, target :: Int | r } -> Effect Unit
setLinksFromRecords sim links = do
  let flatLinks = Array.concatMap (\l -> [l.source, l.target]) links
  setLinks_ sim flatLinks


-- =============================================================================
-- Force Configuration
-- =============================================================================

-- | Configure many-body (charge) force
configureManyBody :: WASMSimulation -> ManyBodyConfig -> Effect Unit
configureManyBody = configureManyBody_

-- | Configure link (spring) force
configureLinks :: WASMSimulation -> LinkConfig -> Effect Unit
configureLinks = configureLinks_

-- | Configure center force
configureCenter :: WASMSimulation -> CenterConfig -> Effect Unit
configureCenter = configureCenter_

-- | Enable/disable forces individually
enableForces :: WASMSimulation -> { manyBody :: Boolean, links :: Boolean, center :: Boolean } -> Effect Unit
enableForces sim cfg = enableForces_ sim cfg.manyBody cfg.links cfg.center


-- =============================================================================
-- Simulation Control
-- =============================================================================

-- | Set alpha (temperature). Higher = more movement.
setAlpha :: WASMSimulation -> Number -> Effect Unit
setAlpha = setAlpha_

-- | Get current alpha
getAlpha :: WASMSimulation -> Effect Number
getAlpha = getAlpha_

-- | Set alpha decay rate
setAlphaDecay :: WASMSimulation -> Number -> Effect Unit
setAlphaDecay = setAlphaDecay_

-- | Set velocity decay (friction). 0.6 means 40% decay per tick.
setVelocityDecay :: WASMSimulation -> Number -> Effect Unit
setVelocityDecay = setVelocityDecay_

-- | Reheat simulation (reset alpha to 1.0)
reheat :: WASMSimulation -> Effect Unit
reheat = reheat_

-- | Run a single simulation tick. Returns new alpha value.
tick :: WASMSimulation -> Effect Number
tick = tick_

-- | Run multiple ticks. Stops early if alpha < alphaMin.
tickN :: WASMSimulation -> Int -> Effect Number
tickN = tickN_

-- | Check if simulation is still running (alpha >= alphaMin)
isRunning :: WASMSimulation -> Effect Boolean
isRunning = isRunning_


-- =============================================================================
-- Queries
-- =============================================================================

-- | Get number of nodes
nodeCount :: WASMSimulation -> Effect Int
nodeCount = nodeCount_

-- | Get number of links
linkCount :: WASMSimulation -> Effect Int
linkCount = linkCount_


-- =============================================================================
-- Node Array Sync
-- =============================================================================

-- | Copy positions from PureScript node array to WASM
syncPositionsToWasm :: forall r. WASMSimulation -> Array { x :: Number, y :: Number | r } -> Effect Unit
syncPositionsToWasm = syncPositionsToWasm_

-- | Copy positions from WASM back to PureScript node array.
-- | Warning: This mutates the input array!
syncPositionsFromWasm :: forall r. WASMSimulation -> Array { x :: Number, y :: Number, vx :: Number, vy :: Number | r } -> Effect (Array { x :: Number, y :: Number, vx :: Number, vy :: Number | r })
syncPositionsFromWasm = syncPositionsFromWasm_
