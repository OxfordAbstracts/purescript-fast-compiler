-- | Simulation Group - Multiple Synchronized Simulations
-- |
-- | Manages multiple force simulations with a single shared animation loop.
-- | Each simulation can be individually activated/deactivated.
-- |
-- | Use cases:
-- | - Multiple graph visualizations that need synchronized updates
-- | - Comparative views (same data, different force configurations)
-- | - Puzzle games with multiple interacting graphs
-- |
-- | Example:
-- | ```purescript
-- | -- Create 6 simulations
-- | group <- createGroup (Array.replicate 6 defaultConfig)
-- |
-- | -- Set nodes for each
-- | for_ (Array.range 0 5) \i -> do
-- |   setNodesAt i myNodes group
-- |
-- | -- Subscribe to tick events (single subscription for all 6)
-- | emitter <- subscribeToGroup group
-- | void $ H.subscribe $ emitter <#> \_ -> SimTick
-- |
-- | -- Start the shared animation loop
-- | startGroup group
-- |
-- | -- Pause simulation 2 while others continue
-- | setSimActive 2 false group
-- | ```
module Hylograph.Kernel.D3.SimulationGroup
  ( -- * Types
    SimulationGroup
  , GroupConfig
  , defaultGroupConfig
    -- * Lifecycle
  , createGroup
  , createGroupWithCallbacks
    -- * Running
  , startGroup
  , stopGroup
  , tickGroup
  , reheatAll
  , reheatAt
    -- * Per-Simulation Control
  , setSimActive
  , setAllActive
  , isSimActive
  , getActiveFlags
    -- * Data Management
  , setNodesAt
  , setLinksAt
  , getNodesAt
  , getSimulationAt
  , getSimulationCount
    -- * Force Configuration
  , applySetupAt
  , applySetupAll
    -- * Callbacks
  , getGroupCallbacks
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (for)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Hylograph.Kernel.D3.Core as Core
import Hylograph.Kernel.D3.Events (SimulationCallbacks, SimulationEvent(..), defaultCallbacks)
import Hylograph.Kernel.D3.Simulation (Simulation, SimulationNode, SimConfig, defaultConfig)
import Hylograph.Kernel.D3.Simulation as Sim
import Hylograph.Kernel.D3.Setup (Setup)
import Hylograph.Kernel.D3.Setup as Setup

-- =============================================================================
-- Types
-- =============================================================================

-- | A group of simulations sharing a single animation loop
type SimulationGroup row linkRow =
  { simulations :: Array (Simulation row linkRow)
  , activeFlags :: Ref (Array Boolean)  -- which sims to tick
  , running :: Ref Boolean              -- is animation loop running
  , cancelAnimation :: Ref (Effect Unit)
  , callbacks :: Maybe SimulationCallbacks
  }

-- | Configuration for creating a group
type GroupConfig =
  { count :: Int
  , simConfig :: SimConfig
  }

-- | Default group configuration
defaultGroupConfig :: GroupConfig
defaultGroupConfig =
  { count: 1
  , simConfig: defaultConfig
  }

-- =============================================================================
-- Lifecycle
-- =============================================================================

-- | Create a group of simulations (without callbacks)
createGroup :: forall row linkRow. Int -> SimConfig -> Effect (SimulationGroup row linkRow)
createGroup count config = do
  sims <- for (Array.range 0 (count - 1)) \_ -> Sim.create config
  activeRef <- Ref.new (Array.replicate count true)  -- all active by default
  runningRef <- Ref.new false
  cancelRef <- Ref.new (pure unit)
  pure
    { simulations: sims
    , activeFlags: activeRef
    , running: runningRef
    , cancelAnimation: cancelRef
    , callbacks: Nothing
    }

-- | Create a group with callbacks (for Halogen subscription)
createGroupWithCallbacks :: forall row linkRow.
  Int
  -> SimConfig
  -> SimulationCallbacks
  -> Effect (SimulationGroup row linkRow)
createGroupWithCallbacks count config cbs = do
  sims <- for (Array.range 0 (count - 1)) \_ -> Sim.create config
  activeRef <- Ref.new (Array.replicate count true)
  runningRef <- Ref.new false
  cancelRef <- Ref.new (pure unit)
  pure
    { simulations: sims
    , activeFlags: activeRef
    , running: runningRef
    , cancelAnimation: cancelRef
    , callbacks: Just cbs
    }

-- =============================================================================
-- Running
-- =============================================================================

-- | Start the shared animation loop
-- | Only active simulations are ticked each frame
startGroup :: forall row linkRow. SimulationGroup row linkRow -> Effect Unit
startGroup group = do
  alreadyRunning <- Ref.read group.running
  unless alreadyRunning do
    Ref.write true group.running

    -- Fire onStart callback
    invokeStartCallback group

    -- Start single animation loop for all
    cancel <- Core.startAnimation \_ -> do
      running <- Ref.read group.running
      if running
        then do
          anyActive <- tickGroup group

          -- Fire tick callback
          invokeTickCallback group

          -- Continue if any simulation still has energy
          pure anyActive
        else pure false

    Ref.write cancel group.cancelAnimation

-- | Stop the animation loop
stopGroup :: forall row linkRow. SimulationGroup row linkRow -> Effect Unit
stopGroup group = do
  Ref.write false group.running
  cancel <- Ref.read group.cancelAnimation
  cancel
  invokeStopCallback group

-- | Tick all active simulations once
-- | Returns true if any simulation still has alpha > 0
tickGroup :: forall row linkRow. SimulationGroup row linkRow -> Effect Boolean
tickGroup group = do
  activeFlags <- Ref.read group.activeFlags
  results <- for (Array.zipWith Tuple group.simulations activeFlags) \(Tuple sim isActive) ->
    if isActive
      then do
        alpha <- Sim.tick sim
        pure (alpha > 0.0)
      else pure false
  pure $ Array.any identity results

-- | Reheat all active simulations
reheatAll :: forall row linkRow. SimulationGroup row linkRow -> Effect Unit
reheatAll group = do
  activeFlags <- Ref.read group.activeFlags
  for_ (Array.zipWith Tuple group.simulations activeFlags) \(Tuple sim isActive) ->
    when isActive $ Ref.write 1.0 sim.alpha

  -- Restart if not running
  running <- Ref.read group.running
  unless running $ startGroup group

-- | Reheat a specific simulation
reheatAt :: forall row linkRow. Int -> SimulationGroup row linkRow -> Effect Unit
reheatAt idx group = case Array.index group.simulations idx of
  Nothing -> pure unit
  Just sim -> do
    Ref.write 1.0 sim.alpha
    running <- Ref.read group.running
    unless running $ startGroup group

-- =============================================================================
-- Per-Simulation Control
-- =============================================================================

-- | Set whether a specific simulation is active (will be ticked)
setSimActive :: forall row linkRow. Int -> Boolean -> SimulationGroup row linkRow -> Effect Unit
setSimActive idx active group = do
  flags <- Ref.read group.activeFlags
  case Array.updateAt idx active flags of
    Nothing -> pure unit
    Just newFlags -> Ref.write newFlags group.activeFlags

-- | Set all simulations active or inactive
setAllActive :: forall row linkRow. Boolean -> SimulationGroup row linkRow -> Effect Unit
setAllActive active group = do
  let count = Array.length group.simulations
  Ref.write (Array.replicate count active) group.activeFlags

-- | Check if a simulation is active
isSimActive :: forall row linkRow. Int -> SimulationGroup row linkRow -> Effect Boolean
isSimActive idx group = do
  flags <- Ref.read group.activeFlags
  pure $ fromMaybe false $ Array.index flags idx

-- | Get all active flags
getActiveFlags :: forall row linkRow. SimulationGroup row linkRow -> Effect (Array Boolean)
getActiveFlags group = Ref.read group.activeFlags

-- =============================================================================
-- Data Management
-- =============================================================================

-- | Set nodes for a specific simulation
setNodesAt :: forall row linkRow.
  Int
  -> Array (SimulationNode row)
  -> SimulationGroup row linkRow
  -> Effect Unit
setNodesAt idx nodes group = case Array.index group.simulations idx of
  Nothing -> pure unit
  Just sim -> Sim.setNodes nodes sim

-- | Set links for a specific simulation
setLinksAt :: forall row linkRow.
  Int
  -> Array { source :: Int, target :: Int | linkRow }
  -> SimulationGroup row linkRow
  -> Effect Unit
setLinksAt idx links group = case Array.index group.simulations idx of
  Nothing -> pure unit
  Just sim -> Sim.setLinks links sim

-- | Get nodes from a specific simulation
getNodesAt :: forall row linkRow.
  Int
  -> SimulationGroup row linkRow
  -> Effect (Maybe (Array (SimulationNode row)))
getNodesAt idx group = case Array.index group.simulations idx of
  Nothing -> pure Nothing
  Just sim -> Just <$> Sim.getNodes sim

-- | Get a simulation by index (for direct access)
getSimulationAt :: forall row linkRow.
  Int
  -> SimulationGroup row linkRow
  -> Maybe (Simulation row linkRow)
getSimulationAt idx group = Array.index group.simulations idx

-- | Get the number of simulations in the group
getSimulationCount :: forall row linkRow. SimulationGroup row linkRow -> Int
getSimulationCount group = Array.length group.simulations

-- =============================================================================
-- Force Configuration
-- =============================================================================

-- | Apply a force setup to a specific simulation
applySetupAt :: forall row linkRow.
  Int
  -> Setup (SimulationNode row)
  -> SimulationGroup row linkRow
  -> Effect Unit
applySetupAt idx setup group = case Array.index group.simulations idx of
  Nothing -> pure unit
  Just sim -> Setup.applySetup setup sim

-- | Apply a force setup to all simulations
applySetupAll :: forall row linkRow.
  Setup (SimulationNode row)
  -> SimulationGroup row linkRow
  -> Effect Unit
applySetupAll setup group =
  for_ group.simulations \sim -> Setup.applySetup setup sim

-- =============================================================================
-- Callbacks
-- =============================================================================

-- | Get the group's callbacks (for Halogen subscription)
getGroupCallbacks :: forall row linkRow.
  SimulationGroup row linkRow
  -> Maybe SimulationCallbacks
getGroupCallbacks group = group.callbacks

-- =============================================================================
-- Internal Callback Helpers
-- =============================================================================

invokeStartCallback :: forall row linkRow. SimulationGroup row linkRow -> Effect Unit
invokeStartCallback group = case group.callbacks of
  Nothing -> pure unit
  Just cbs -> do
    callback <- Ref.read cbs.onStart
    callback

invokeStopCallback :: forall row linkRow. SimulationGroup row linkRow -> Effect Unit
invokeStopCallback group = case group.callbacks of
  Nothing -> pure unit
  Just cbs -> do
    callback <- Ref.read cbs.onStop
    callback

invokeTickCallback :: forall row linkRow. SimulationGroup row linkRow -> Effect Unit
invokeTickCallback group = case group.callbacks of
  Nothing -> pure unit
  Just cbs -> do
    callback <- Ref.read cbs.onTick
    callback
