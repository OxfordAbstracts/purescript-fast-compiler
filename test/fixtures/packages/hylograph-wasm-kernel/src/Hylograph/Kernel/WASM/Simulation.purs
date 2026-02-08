-- | WASM Simulation with D3-compatible API
-- |
-- | High-level simulation wrapper that provides the same API as
-- | Hylograph.Kernel.D3.Simulation, enabling drop-in replacement.
-- |
-- | Key features:
-- | - Animation loop via requestAnimationFrame
-- | - Callback system for Halogen integration
-- | - Position sync between PureScript and WASM
-- |
-- | Usage:
-- | ```purescript
-- | import Hylograph.Kernel.WASM.Simulation as Sim
-- | import Hylograph.Kernel.WASM.Events (defaultCallbacks)
-- |
-- | main = do
-- |   callbacks <- defaultCallbacks
-- |   sim <- Sim.createWithCallbacks Sim.defaultConfig callbacks
-- |   Sim.setNodes myNodes sim
-- |   Sim.setLinks myLinks sim
-- |   Sim.start sim
-- | ```
module Hylograph.Kernel.WASM.Simulation
  ( -- * Types
    Simulation
  , SimulationNode
  , SimConfig
  , NodeID
  , Link
    -- * Configuration
  , defaultConfig
    -- * Lifecycle
  , create
  , createWithCallbacks
  , start
  , stop
  , reheat
    -- * Data
  , setNodes
  , setLinks
  , getNodes
  , getLinks
    -- * State
  , isRunning
  , getAlpha
    -- * Callbacks
  , getCallbacks
    -- * Force Configuration
  , configureManyBody
  , configureLinks
  , configureCenter
  , configureForceX
  , configureForceY
  , configureCollide
  , enableForces
  , enableForcesAll
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref as Ref
import Hylograph.Kernel.WASM.Events (SimulationCallbacks)
import Hylograph.Kernel.WASM.FFI as WASM

-- =============================================================================
-- FFI for Animation Loop
-- =============================================================================

foreign import requestAnimationFrame_ :: Effect Unit -> Effect Int
foreign import cancelAnimationFrame_ :: Int -> Effect Unit

-- =============================================================================
-- Types
-- =============================================================================

-- | Node ID type (matches D3 kernel)
type NodeID = Int

-- | Simulation node with standard fields.
-- | Row polymorphic to allow extra user data.
-- | Note: fx/fy use Number with NaN for "not fixed" (D3 convention)
type SimulationNode r =
  { id :: NodeID
  , x :: Number
  , y :: Number
  , vx :: Number
  , vy :: Number
  , fx :: Number  -- Fixed x (NaN if not fixed)
  , fy :: Number  -- Fixed y (NaN if not fixed)
  | r
  }

-- | Link type for the simulation
type Link r = { source :: Int, target :: Int | r }

-- | Simulation configuration
type SimConfig =
  { alphaMin :: Number      -- Stop when alpha falls below this (default: 0.001)
  , alphaDecay :: Number    -- How fast alpha decays (default: 0.0228)
  , alphaTarget :: Number   -- Target alpha for reheat (default: 0.0)
  , velocityDecay :: Number -- Velocity damping (default: 0.4)
  , ticksPerFrame :: Int    -- Physics ticks per render frame (default: 3)
  }

-- | The Simulation handle
-- | Internal refs are implementation details - users interact via functions
type Simulation r linkRow =
  { wasmSim :: WASM.WASMSimulation
  , nodes :: Ref.Ref (Array (SimulationNode r))
  , links :: Ref.Ref (Array (Link linkRow))
  , running :: Ref.Ref Boolean
  , alpha :: Ref.Ref Number
  , prevAlpha :: Ref.Ref Number
  , animationId :: Ref.Ref (Maybe Int)
  , config :: SimConfig
  , callbacks :: Maybe SimulationCallbacks  -- Direct field, not Ref
  }

-- =============================================================================
-- Configuration
-- =============================================================================

-- | Default simulation configuration
defaultConfig :: SimConfig
defaultConfig =
  { alphaMin: 0.001
  , alphaDecay: 0.0228
  , alphaTarget: 0.0
  , velocityDecay: 0.4
  , ticksPerFrame: 10  -- Run 10 physics ticks per render frame for better performance
  }

-- =============================================================================
-- Lifecycle
-- =============================================================================

-- | Create a simulation without callbacks
create :: forall r linkRow. SimConfig -> Effect (Simulation r linkRow)
create config = createWithCallbacksMaybe config Nothing

-- | Create a simulation with callbacks (for Halogen integration)
createWithCallbacks :: forall r linkRow.
  SimConfig
  -> SimulationCallbacks
  -> Effect (Simulation r linkRow)
createWithCallbacks config cbs = createWithCallbacksMaybe config (Just cbs)

-- | Internal: Create simulation with optional callbacks
createWithCallbacksMaybe :: forall r linkRow.
  SimConfig
  -> Maybe SimulationCallbacks
  -> Effect (Simulation r linkRow)
createWithCallbacksMaybe config mcbs = do
  wasmSim <- WASM.create 0  -- Start with 0 nodes
  nodes <- Ref.new []
  links <- Ref.new []
  running <- Ref.new false
  alpha <- Ref.new 1.0
  prevAlpha <- Ref.new 1.0
  animationId <- Ref.new Nothing

  -- Configure WASM
  WASM.setAlphaDecay wasmSim config.alphaDecay
  WASM.setVelocityDecay wasmSim config.velocityDecay

  pure { wasmSim, nodes, links, running, alpha, prevAlpha, animationId, config, callbacks: mcbs }

-- | Start the animation loop
start :: forall r linkRow. Simulation r linkRow -> Effect Unit
start sim = do
  running <- Ref.read sim.running
  unless running do
    Ref.write true sim.running

    -- Fire start callback
    case sim.callbacks of
      Just cbs -> do
        cb <- Ref.read cbs.onStart
        cb
      Nothing -> pure unit

    -- Start animation loop
    runAnimationLoop sim

-- | Stop the animation loop
stop :: forall r linkRow. Simulation r linkRow -> Effect Unit
stop sim = do
  Ref.write false sim.running

  -- Cancel pending animation frame
  mAnimId <- Ref.read sim.animationId
  case mAnimId of
    Just animId -> cancelAnimationFrame_ animId
    Nothing -> pure unit
  Ref.write Nothing sim.animationId

  -- Fire stop callback
  case sim.callbacks of
    Just cbs -> do
      cb <- Ref.read cbs.onStop
      cb
    Nothing -> pure unit

-- | Reheat the simulation (reset alpha and restart)
reheat :: forall r linkRow. Simulation r linkRow -> Effect Unit
reheat sim = do
  Ref.write 1.0 sim.alpha
  WASM.setAlpha sim.wasmSim 1.0

  running <- Ref.read sim.running
  unless running do
    start sim

-- =============================================================================
-- Animation Loop (internal)
-- =============================================================================

runAnimationLoop :: forall r linkRow. Simulation r linkRow -> Effect Unit
runAnimationLoop sim = do
  running <- Ref.read sim.running
  when running do
    -- Run multiple WASM ticks per frame for better performance
    -- Only sync/render once at the end
    newAlpha <- runTickBatch sim.config.ticksPerFrame sim.wasmSim sim.config.alphaMin
    Ref.write newAlpha sim.alpha

    -- Sync positions from WASM to PureScript nodes (once per frame)
    nodes <- Ref.read sim.nodes
    updatedNodes <- WASM.syncPositionsFromWasm sim.wasmSim nodes
    Ref.write updatedNodes sim.nodes

    -- Fire tick callback (once per frame, after all physics ticks)
    case sim.callbacks of
      Just cbs -> do
        tickCb <- Ref.read cbs.onTick
        tickCb

        -- Check alpha thresholds
        prev <- Ref.read sim.prevAlpha
        checkAlphaThresholds prev newAlpha cbs
        Ref.write newAlpha sim.prevAlpha
      Nothing -> pure unit

    -- Check if simulation should stop
    if newAlpha < sim.config.alphaMin
      then stop sim
      else do
        -- Schedule next frame
        animId <- requestAnimationFrame_ (runAnimationLoop sim)
        Ref.write (Just animId) sim.animationId

-- | Run multiple physics ticks, return final alpha
runTickBatch :: Int -> WASM.WASMSimulation -> Number -> Effect Number
runTickBatch 0 _ _ = pure 1.0
runTickBatch n wasmSim alphaMin = go n 1.0
  where
    go :: Int -> Number -> Effect Number
    go 0 alpha = pure alpha
    go remaining _ = do
      alpha <- WASM.tick wasmSim
      if alpha < alphaMin
        then pure alpha  -- Stop early if converged
        else go (remaining - 1) alpha

-- | Check and fire alpha threshold callbacks
checkAlphaThresholds :: Number -> Number -> SimulationCallbacks -> Effect Unit
checkAlphaThresholds prev current cbs = do
  let thresholds = [0.5, 0.1, 0.01]
  let crossed = Array.filter (\t -> prev >= t && current < t) thresholds
  case Array.last crossed of
    Just t -> do
      alphaCb <- Ref.read cbs.onAlphaThreshold
      alphaCb t
    Nothing -> pure unit

-- =============================================================================
-- Data Management
-- =============================================================================

-- | Set/replace all nodes
-- | Note: We don't sync positions from PureScript to WASM because:
-- | 1. WASM initializes nodes in a nice phyllotaxis pattern
-- | 2. PureScript nodes typically start at (0,0) which causes convergence issues
-- | The WASM simulation will compute positions and we read them back via getNodes.
setNodes :: forall r linkRow.
  Array (SimulationNode r)
  -> Simulation r linkRow
  -> Effect Unit
setNodes newNodes sim = do
  WASM.setNodeCount sim.wasmSim (Array.length newNodes)
  -- Don't sync positions to WASM - let it use phyllotaxis initialization
  -- WASM.syncPositionsToWasm sim.wasmSim newNodes
  Ref.write newNodes sim.nodes

-- | Set/replace all links
setLinks :: forall r linkRow.
  Array (Link linkRow)
  -> Simulation r linkRow
  -> Effect Unit
setLinks newLinks sim = do
  WASM.setLinksFromRecords sim.wasmSim newLinks
  Ref.write newLinks sim.links

-- | Get current nodes with positions
getNodes :: forall r linkRow. Simulation r linkRow -> Effect (Array (SimulationNode r))
getNodes sim = do
  nodes <- Ref.read sim.nodes
  WASM.syncPositionsFromWasm sim.wasmSim nodes

-- | Get current links
getLinks :: forall r linkRow. Simulation r linkRow -> Effect (Array (Link linkRow))
getLinks sim = Ref.read sim.links

-- =============================================================================
-- State
-- =============================================================================

-- | Check if simulation is running
isRunning :: forall r linkRow. Simulation r linkRow -> Effect Boolean
isRunning sim = Ref.read sim.running

-- | Get current alpha value
getAlpha :: forall r linkRow. Simulation r linkRow -> Effect Number
getAlpha sim = Ref.read sim.alpha

-- =============================================================================
-- Callbacks
-- =============================================================================

-- | Get callbacks (for Halogen integration)
-- | Returns the callbacks set at creation time
getCallbacks :: forall r linkRow. Simulation r linkRow -> Maybe SimulationCallbacks
getCallbacks sim = sim.callbacks

-- =============================================================================
-- Force Configuration
-- =============================================================================

-- | Configure many-body force
configureManyBody :: forall r linkRow.
  WASM.ManyBodyConfig
  -> Simulation r linkRow
  -> Effect Unit
configureManyBody config sim = WASM.configureManyBody sim.wasmSim config

-- | Configure link force
configureLinks :: forall r linkRow.
  WASM.LinkConfig
  -> Simulation r linkRow
  -> Effect Unit
configureLinks config sim = WASM.configureLinks sim.wasmSim config

-- | Configure center force
configureCenter :: forall r linkRow.
  WASM.CenterConfig
  -> Simulation r linkRow
  -> Effect Unit
configureCenter config sim = WASM.configureCenter sim.wasmSim config

-- | Enable/disable forces (original 3)
enableForces :: forall r linkRow.
  { manyBody :: Boolean, links :: Boolean, center :: Boolean }
  -> Simulation r linkRow
  -> Effect Unit
enableForces config sim = WASM.enableForces sim.wasmSim config

-- | Configure forceX (pull toward x position)
configureForceX :: forall r linkRow.
  WASM.ForceXConfig
  -> Simulation r linkRow
  -> Effect Unit
configureForceX config sim = WASM.configureForceX sim.wasmSim config

-- | Configure forceY (pull toward y position)
configureForceY :: forall r linkRow.
  WASM.ForceYConfig
  -> Simulation r linkRow
  -> Effect Unit
configureForceY config sim = WASM.configureForceY sim.wasmSim config

-- | Configure collide force (prevent node overlap)
configureCollide :: forall r linkRow.
  WASM.CollideConfig
  -> Simulation r linkRow
  -> Effect Unit
configureCollide config sim = WASM.configureCollide sim.wasmSim config

-- | Enable/disable all forces including new ones
enableForcesAll :: forall r linkRow.
  { manyBody :: Boolean, links :: Boolean, center :: Boolean
  , forceX :: Boolean, forceY :: Boolean, collide :: Boolean }
  -> Simulation r linkRow
  -> Effect Unit
enableForcesAll config sim = WASM.enableForcesAll sim.wasmSim config
