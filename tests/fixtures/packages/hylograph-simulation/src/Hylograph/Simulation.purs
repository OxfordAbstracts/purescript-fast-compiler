-- | Hylograph Force Simulation
-- |
-- | High-level API for running force-directed simulations.
-- | Supports both D3.js and WASM physics engines with the same interface.
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hylograph.Simulation (runSimulation, Engine(..), SimulationEvent(..))
-- | import Hylograph.Simulation.Emitter (subscribe)
-- |
-- | main = do
-- |   -- Run simulation - returns handle AND event emitter
-- |   { handle, events } <- runSimulation
-- |     { engine: D3  -- or WASM (same config!)
-- |     , setup: setup "physics"
-- |         [ manyBody "charge" # withStrength (static (-30.0))
-- |         , center "center"
-- |         ]
-- |     , nodes: myNodes
-- |     , links: []
-- |     , container: "#my-svg"
-- |     , alphaMin: 0.001
-- |     }
-- |
-- |   -- Subscribe to events (framework-agnostic)
-- |   unsubscribe <- subscribe events \event -> case event of
-- |     Tick { alpha } -> log $ "Alpha: " <> show alpha
-- |     Completed -> log "Simulation converged!"
-- |     _ -> pure unit
-- |
-- |   -- Get nodes for rendering (use HATS or your own rendering)
-- |   nodes <- handle.getNodes
-- |
-- |   -- Update data (GUP semantics, auto-reheat)
-- |   result <- handle.updateData newNodes newLinks
-- | ```
-- |
-- | ## Framework Integration
-- |
-- | **Halogen**: Use `toHalogenEmitter` from `Hylograph.Simulation.Halogen`
-- | **React**: Use `subscribe` in a `useEffect` hook with cleanup
-- | **Vanilla**: Just call `subscribe` directly
module Hylograph.Simulation
  ( -- * Main Entry Point
    runSimulation
  , SimulationResult

    -- * Configuration
  , SimulationConfig
  , Engine(..)

    -- * Handle (for controlling the simulation)
  , SimulationHandle

    -- * Position interpolation types
  , PositionMap

    -- * Events (framework-agnostic)
  , module EmitterExports

    -- * WASM Initialization
  , initWASM

    -- * Re-exports for convenience
  , module SetupExports
  , module SimNodeExports
  ) where

import Prelude

import Data.Array as Array
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref as Ref

-- Coordinator
import Hylograph.Transition.Coordinator as Coord

-- Emitter
import Hylograph.Simulation.Emitter as Emitter
-- For local use
import Hylograph.Simulation.Emitter (SimulationEmitter, SimulationEvent(..))
-- For re-export
import Hylograph.Simulation.Emitter (SimulationEmitter, SimulationEvent(..), subscribe) as EmitterExports

-- D3 Force Engine
import Hylograph.ForceEngine.Simulation as D3Sim
import Hylograph.ForceEngine.Setup as D3Setup
import Hylograph.ForceEngine.Setup
  ( Setup
  , GUPResult
  , GUPLinkResult
  , setup
  , manyBody
  , collide
  , link
  , center
  , positionX
  , positionY
  , radial
  , withStrength
  , withRadius
  , withX
  , withY
  , withDistance
  , withTheta
  , withIterations
  , withFilter
  , withDistanceMin
  , withDistanceMax
  , static
  , dynamic
  ) as SetupExports

-- Import types we need locally (also re-exported via SetupExports)
import Hylograph.ForceEngine.Setup (GUPResult, GUPLinkResult)

-- WASM Force Engine
import Hylograph.ForceEngine.Setup.WASM as WASMSetup

-- Node type re-export
import Hylograph.ForceEngine.Simulation (SimulationNode) as SimNodeExports

-- =============================================================================
-- Types
-- =============================================================================

-- | Position map for interpolation - keyed by node ID (as string)
type PositionMap = D3Sim.PositionMap

-- | Physics engine selection
data Engine = D3 | WASM

-- | Configuration for running a simulation
-- |
-- | Note: There's no `onComplete` callback - use the `events` emitter instead.
-- | This keeps the API framework-agnostic.
-- |
-- | Rendering is handled externally via the Tick event and `handle.getNodes`.
-- | Use HATS or any other rendering approach to render node positions on each tick.
type SimulationConfig r =
  { engine :: Engine
  , setup :: D3Setup.Setup (D3Sim.SimulationNode r)
  , nodes :: Array (D3Sim.SimulationNode r)
  , links :: Array { source :: Int, target :: Int }
  , container :: String  -- CSS selector for SVG container (used for data tracking)
  , alphaMin :: Number   -- Convergence threshold (default: 0.001)
  }

-- | Result returned by runSimulation
-- |
-- | - `handle`: Control the simulation (update data, stop, start, etc.)
-- | - `events`: Subscribe to simulation events (Tick, Completed, etc.)
type SimulationResult r =
  { handle :: SimulationHandle r
  , events :: SimulationEmitter
  }

-- | Handle for controlling the simulation
type SimulationHandle r =
  { -- | Update nodes and links with GUP semantics (auto-reheats)
    updateData
      :: Array (D3Sim.SimulationNode r)
      -> Array { source :: Int, target :: Int }
      -> Effect { nodes :: GUPResult (D3Sim.SimulationNode r), links :: GUPLinkResult () }

    -- | Update force configuration (auto-reheats)
  , updateSetup :: D3Setup.Setup (D3Sim.SimulationNode r) -> Effect Unit

    -- | Get current nodes with positions
  , getNodes :: Effect (Array (D3Sim.SimulationNode r))

    -- | Get current alpha value
  , getAlpha :: Effect Number

    -- | Stop the simulation
  , stop :: Effect Unit

    -- | Start/resume the simulation
  , start :: Effect Unit

    -- | Reheat the simulation (reset alpha to 1.0)
  , reheat :: Effect Unit

    -- | Interpolate node positions between start and target positions.
    -- | Progress should be 0.0 to 1.0 (apply easing before calling).
    -- | Used for animated transitions like quadrant layout.
  , interpolatePositions :: D3Sim.PositionMap -> D3Sim.PositionMap -> Number -> Effect Unit

    -- | Pin all nodes at their current positions (fx = x, fy = y).
    -- | Use before starting a transition to freeze current state.
  , pinNodes :: Effect Unit

    -- | Unpin all nodes (fx = null, fy = null).
    -- | Use after transition to let forces take over again.
  , unpinNodes :: Effect Unit
  }

-- =============================================================================
-- WASM Initialization
-- =============================================================================

-- | Initialize the WASM physics engine.
-- | Call once at application startup before using Engine.WASM.
-- |
-- | Example: `initWASM "./pkg/force_kernel.js"`
initWASM :: String -> Aff Unit
initWASM = WASMSetup.initWasm

-- =============================================================================
-- Main Entry Point
-- =============================================================================

-- | Run a force simulation with Hylograph visualization.
-- |
-- | Returns both a handle for controlling the simulation AND an event emitter
-- | for subscribing to simulation events. This design is framework-agnostic:
-- |
-- | - The emitter works with Halogen, React, or vanilla JS
-- | - Events include Tick, Started, Stopped, and Completed
-- | - The same code works for both D3 and WASM engines
-- | Note: No Ord constraint required! We use renderTreeKeyed with a key function
-- | based on node.id, which doesn't require Ord on the datum type. This allows
-- | SimulationNode r (an extensible record) to work without needing Ord derivation.
runSimulation
  :: forall r
   . SimulationConfig r
  -> Effect (SimulationResult r)
runSimulation config = case config.engine of
  D3 -> runD3Simulation config
  WASM -> runWASMSimulation config

-- =============================================================================
-- D3 Engine Implementation
-- =============================================================================

runD3Simulation
  :: forall r
   . SimulationConfig r
  -> Effect (SimulationResult r)
runD3Simulation config = do
  -- Create emitter for events
  { emitter, handle: emitterHandle } <- Emitter.create

  -- Create simulation with alphaDecay from setup
  -- This is important because sim.config is immutable after creation
  let simConfig = D3Sim.defaultConfig
        { alphaDecay = config.setup.params.alphaDecay
        , alphaMin = config.alphaMin
        }
  sim <- D3Sim.create simConfig

  -- Apply initial setup with data
  _ <- D3Setup.applySetupWithData config.setup config.nodes config.links sim

  -- Store current setup for updates
  setupRef <- Ref.new config.setup

  -- Store alpha for getAlpha
  alphaRef <- Ref.new 1.0

  -- Create coordinator
  coord <- Coord.create
  coordRef <- Ref.new coord

  -- Track if running
  runningRef <- Ref.new true

  -- Emit Started event
  Emitter.emit emitterHandle Started

  -- Register consumer
  _ <- Coord.register coord
    { tick: d3Consumer sim emitterHandle alphaRef config.alphaMin
    , onComplete: do
        Ref.write false runningRef
        Emitter.emit emitterHandle Completed
    }

  -- Start coordinator
  Coord.start coord

  -- Return handle and emitter
  pure
    { events: emitter
    , handle:
        { updateData: \nodes links -> do
            currentSetup <- Ref.read setupRef
            result <- D3Setup.applySetupWithData currentSetup nodes links sim
            D3Sim.reheat sim
            Ref.write 1.0 alphaRef
            Emitter.emit emitterHandle Started
            -- Restart coordinator if simulation has completed
            running <- Ref.read runningRef
            unless running do
              Ref.write true runningRef
              -- Stop old coordinator and create new one
              oldCoord <- Ref.read coordRef
              Coord.stop oldCoord
              c <- Coord.create
              Ref.write c coordRef
              _ <- Coord.register c
                { tick: d3Consumer sim emitterHandle alphaRef config.alphaMin
                , onComplete: do
                    Ref.write false runningRef
                    Emitter.emit emitterHandle Completed
                }
              Coord.start c
            pure result

        , updateSetup: \newSetup -> do
            Ref.write newSetup setupRef
            D3Setup.applySetup newSetup sim
            D3Sim.reheat sim
            Ref.write 1.0 alphaRef
            Emitter.emit emitterHandle Started
            -- Restart coordinator if simulation has completed
            running <- Ref.read runningRef
            unless running do
              Ref.write true runningRef
              -- Stop old coordinator and create new one
              oldCoord <- Ref.read coordRef
              Coord.stop oldCoord
              c <- Coord.create
              Ref.write c coordRef
              _ <- Coord.register c
                { tick: d3Consumer sim emitterHandle alphaRef config.alphaMin
                , onComplete: do
                    Ref.write false runningRef
                    Emitter.emit emitterHandle Completed
                }
              Coord.start c

        , getNodes: D3Sim.getNodes sim

        , getAlpha: Ref.read alphaRef

        , stop: do
            running <- Ref.read runningRef
            when running do
              Ref.write false runningRef
              Emitter.emit emitterHandle Stopped

        , start: do
            running <- Ref.read runningRef
            unless running do
              D3Sim.reheat sim
              Ref.write 1.0 alphaRef
              Ref.write true runningRef
              Emitter.emit emitterHandle Started
              -- Stop old coordinator before creating new one (prevents CPU spike from multiple RAF loops)
              oldCoord <- Ref.read coordRef
              Coord.stop oldCoord
              -- Re-register and restart
              c <- Coord.create
              Ref.write c coordRef
              _ <- Coord.register c
                { tick: d3Consumer sim emitterHandle alphaRef config.alphaMin
                , onComplete: do
                    Ref.write false runningRef
                    Emitter.emit emitterHandle Completed
                }
              Coord.start c

        , reheat: do
            D3Sim.reheat sim
            Ref.write 1.0 alphaRef
            Emitter.emit emitterHandle Started

        , interpolatePositions: \startPos targetPos progress ->
            D3Sim.interpolatePositionsInPlace startPos targetPos progress sim

        , pinNodes: D3Sim.pinNodesInPlace sim

        , unpinNodes: D3Sim.unpinNodesInPlace sim
        }
    }

-- | D3 consumer for coordinator - emits Tick events
-- | Rendering is handled by callers subscribing to Tick events
d3Consumer
  :: forall r
   . D3Sim.Simulation r ()
  -> Emitter.EmitterHandle
  -> Ref.Ref Number
  -> Number
  -> Coord.Milliseconds
  -> Effect Coord.TickResult
d3Consumer sim emitterHandle alphaRef alphaMin _deltaMs = do
  -- Advance the D3 force simulation by one tick
  alpha <- D3Sim.tick sim
  Ref.write alpha alphaRef
  nodes <- D3Sim.getNodes sim
  Emitter.emit emitterHandle (Tick { alpha, nodeCount: Array.length nodes })
  pure $ if alpha < alphaMin
    then Coord.Completed
    else Coord.Converged alpha

-- =============================================================================
-- WASM Engine Implementation
-- =============================================================================

runWASMSimulation
  :: forall r
   . SimulationConfig r
  -> Effect (SimulationResult r)
runWASMSimulation config = do
  -- Create emitter for events
  { emitter, handle: emitterHandle } <- Emitter.create

  -- Create WASM simulation with initial data
  sim <- WASMSetup.create config.nodes config.links

  -- Apply initial setup
  _ <- WASMSetup.applySetupWithData config.setup config.nodes config.links sim

  -- Store current setup for updates
  setupRef <- Ref.new config.setup

  -- Store alpha for getAlpha
  alphaRef <- Ref.new 1.0

  -- Create coordinator
  coord <- Coord.create
  coordRef <- Ref.new coord

  -- Track if running
  runningRef <- Ref.new true

  -- Emit Started event
  Emitter.emit emitterHandle Started

  -- Register consumer
  _ <- Coord.register coord
    { tick: wasmConsumer sim emitterHandle alphaRef config.alphaMin
    , onComplete: do
        Ref.write false runningRef
        Emitter.emit emitterHandle Completed
    }

  -- Start coordinator
  Coord.start coord

  -- Return handle and emitter
  pure
    { events: emitter
    , handle:
        { updateData: \nodes links -> do
            currentSetup <- Ref.read setupRef
            result <- WASMSetup.applySetupWithData currentSetup nodes links sim
            WASMSetup.reheat sim
            Ref.write 1.0 alphaRef
            Emitter.emit emitterHandle Started
            -- Restart coordinator if simulation has completed
            running <- Ref.read runningRef
            unless running do
              Ref.write true runningRef
              -- Stop old coordinator and create new one
              oldCoord <- Ref.read coordRef
              Coord.stop oldCoord
              c <- Coord.create
              Ref.write c coordRef
              _ <- Coord.register c
                { tick: wasmConsumer sim emitterHandle alphaRef config.alphaMin
                , onComplete: do
                    Ref.write false runningRef
                    Emitter.emit emitterHandle Completed
                }
              Coord.start c
            pure result

        , updateSetup: \newSetup -> do
            Ref.write newSetup setupRef
            WASMSetup.applySetup newSetup sim
            WASMSetup.reheat sim
            Ref.write 1.0 alphaRef
            Emitter.emit emitterHandle Started
            -- Restart coordinator if simulation has completed
            running <- Ref.read runningRef
            unless running do
              Ref.write true runningRef
              -- Stop old coordinator and create new one
              oldCoord <- Ref.read coordRef
              Coord.stop oldCoord
              c <- Coord.create
              Ref.write c coordRef
              _ <- Coord.register c
                { tick: wasmConsumer sim emitterHandle alphaRef config.alphaMin
                , onComplete: do
                    Ref.write false runningRef
                    Emitter.emit emitterHandle Completed
                }
              Coord.start c

        , getNodes: WASMSetup.getNodes sim

        , getAlpha: Ref.read alphaRef

        , stop: do
            running <- Ref.read runningRef
            when running do
              Ref.write false runningRef
              Emitter.emit emitterHandle Stopped

        , start: do
            running <- Ref.read runningRef
            unless running do
              WASMSetup.reheat sim
              Ref.write 1.0 alphaRef
              Ref.write true runningRef
              Emitter.emit emitterHandle Started
              -- Stop old coordinator before creating new one (prevents CPU spike from multiple RAF loops)
              oldCoord <- Ref.read coordRef
              Coord.stop oldCoord
              c <- Coord.create
              Ref.write c coordRef
              _ <- Coord.register c
                { tick: wasmConsumer sim emitterHandle alphaRef config.alphaMin
                , onComplete: do
                    Ref.write false runningRef
                    Emitter.emit emitterHandle Completed
                }
              Coord.start c

        , reheat: do
            WASMSetup.reheat sim
            Ref.write 1.0 alphaRef
            Emitter.emit emitterHandle Started

        -- Position interpolation not yet implemented for WASM engine.
        -- ForcePlayground uses D3 engine, so this is low priority.
        , interpolatePositions: \_ _ _ -> pure unit

        , pinNodes: pure unit

        , unpinNodes: pure unit
        }
    }

-- | WASM consumer for coordinator - emits Tick events
-- | Rendering is handled by callers subscribing to Tick events
wasmConsumer
  :: forall r
   . WASMSetup.WASMSim r
  -> Emitter.EmitterHandle
  -> Ref.Ref Number
  -> Number
  -> Coord.Milliseconds
  -> Effect Coord.TickResult
wasmConsumer sim emitterHandle alphaRef alphaMin _deltaMs = do
  alpha <- WASMSetup.tick sim
  Ref.write alpha alphaRef
  nodes <- WASMSetup.getNodes sim
  Emitter.emit emitterHandle (Tick { alpha, nodeCount: Array.length nodes })
  pure $ if alpha < alphaMin
    then Coord.Completed
    else Coord.Converged alpha
