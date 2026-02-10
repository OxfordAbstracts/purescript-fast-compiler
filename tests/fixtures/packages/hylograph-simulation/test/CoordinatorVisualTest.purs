-- | Coordinator Test
-- |
-- | Visual test of the TickCoordinator with multiple consumers running simultaneously.
-- | Open test/index.html in a browser to see it in action.
module Test.CoordinatorVisualTest where

import Prelude

import Data.Array (uncons, (!!))
import Data.Maybe (Maybe(..))
import Data.Nullable (null) as Nullable
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Ref as Ref
import Hylograph.Transition.Coordinator (Coordinator, Milliseconds, TickResult(..), create, register, start) as C
import Hylograph.Transition.Consumers (transitionConsumer, transitionGroupConsumer, simulationConsumer)
import Hylograph.Transition.Engine as E
import Hylograph.Transition.Easing (EasingType(..))
import Hylograph.Transition.Tick (lerp)
import Hylograph.ForceEngine.Simulation as Sim
import Hylograph.ForceEngine.Types (ForceSpec(..), defaultManyBody, defaultCenter)
import Test.WASMSimulation as WASM

-- =============================================================================
-- FFI for DOM manipulation (minimal)
-- =============================================================================

foreign import getElementById :: String -> Effect DomElement
foreign import setStyle :: DomElement -> String -> String -> Effect Unit
foreign import setTransform :: DomElement -> String -> Effect Unit
foreign import setPosition :: DomElement -> Number -> Number -> Effect Unit
foreign import logValue :: String -> Number -> Effect Unit

foreign import data DomElement :: Type

-- =============================================================================
-- Main Entry Point
-- =============================================================================

main :: Effect Unit
main = launchAff_ do
  liftEffect $ log "TickCoordinator Test Starting..."

  -- Initialize WASM module first (async)
  liftEffect $ log "Initializing WASM force kernel..."
  WASM.initWasm "./wasm-pkg/force_kernel.js"
  liftEffect $ log "WASM initialized!"

  liftEffect do
    -- Create coordinator
    coord <- C.create

    -- Test 1: Opacity transition (box1)
    box1 <- getElementById "box1"
    setupOpacityTest coord box1

    -- Test 2: Width transition (box2)
    box2 <- getElementById "box2"
    setupWidthTest coord box2

    -- Test 3: Grouped x + opacity (box3)
    box3 <- getElementById "box3"
    setupGroupedTest coord box3

    -- Test 4: Staggered circles
    setupStaggeredTest coord

    -- Test 5: D3 Force Simulation
    setupSimulationTest coord

    -- Test 6: WASM Force Simulation (running alongside D3 and transitions!)
    setupWASMSimulationTest coord

    -- Start the coordinator
    log "Starting coordinator with all consumers..."
    C.start coord

    log "All transitions and simulations registered and running!"

-- =============================================================================
-- Test 1: Simple Opacity
-- =============================================================================

setupOpacityTest :: C.Coordinator -> DomElement -> Effect Unit
setupOpacityTest coord element = do
  log "Setting up opacity transition (0 → 1, 500ms)"
  let spec = E.transition { from: 0.0, to: 1.0 } { duration: 500.0, easing: QuadOut }
  stateRef <- Ref.new (E.start spec)

  _ <- C.register coord
    { tick: transitionConsumer stateRef \value -> do
        setStyle element "opacity" (show value)
    , onComplete: log "✓ Opacity transition complete!"
    }
  pure unit

-- =============================================================================
-- Test 2: Width Transition
-- =============================================================================

setupWidthTest :: C.Coordinator -> DomElement -> Effect Unit
setupWidthTest coord element = do
  log "Setting up width transition (50 → 300px, 1000ms)"
  let spec = E.transition { from: 50.0, to: 300.0 } { duration: 1000.0, easing: CubicInOut }
  stateRef <- Ref.new (E.start spec)

  _ <- C.register coord
    { tick: transitionConsumer stateRef \value -> do
        setStyle element "width" (show value <> "px")
    , onComplete: log "✓ Width transition complete!"
    }
  pure unit

-- =============================================================================
-- Test 3: Grouped Transition (X + Opacity together)
-- =============================================================================

setupGroupedTest :: C.Coordinator -> DomElement -> Effect Unit
setupGroupedTest coord element = do
  log "Setting up grouped transition (X + opacity, 800ms)"
  let specs =
        [ E.transition { from: 0.0, to: 200.0 } { duration: 800.0, easing: QuadOut }    -- x position
        , E.transition { from: 0.0, to: 1.0 } { duration: 400.0, easing: Linear }       -- opacity (faster)
        ]
  groupRef <- Ref.new (E.group specs)

  _ <- C.register coord
    { tick: transitionGroupConsumer groupRef \values -> do
        case values of
          [x, opacity] -> do
            setStyle element "opacity" (show opacity)
            setTransform element ("translateX(" <> show x <> "px)")
          _ -> pure unit
    , onComplete: log "✓ Grouped transition complete!"
    }
  pure unit

-- =============================================================================
-- Test 4: Staggered Transitions (5 circles with delays)
-- =============================================================================

setupStaggeredTest :: C.Coordinator -> Effect Unit
setupStaggeredTest coord = do
  log "Setting up staggered transitions (5 circles, 100ms apart)"

  -- Circle 0: no delay
  c0 <- getElementById "circle0"
  setupStaggeredCircle coord c0 0.0

  -- Circle 1: 100ms delay
  c1 <- getElementById "circle1"
  setupStaggeredCircle coord c1 100.0

  -- Circle 2: 200ms delay
  c2 <- getElementById "circle2"
  setupStaggeredCircle coord c2 200.0

  -- Circle 3: 300ms delay
  c3 <- getElementById "circle3"
  setupStaggeredCircle coord c3 300.0

  -- Circle 4: 400ms delay
  c4 <- getElementById "circle4"
  setupStaggeredCircle coord c4 400.0

setupStaggeredCircle :: C.Coordinator -> DomElement -> Number -> Effect Unit
setupStaggeredCircle coord element delayMs = do
  let config = { duration: 300.0, easing: QuadOut, delay: delayMs }
  let spec = E.transitionWith lerp { from: 0.0, to: 1.0 } config
  stateRef <- Ref.new (E.start spec)

  _ <- C.register coord
    { tick: transitionConsumer stateRef \value -> do
        setStyle element "opacity" (show value)
        setTransform element ("scale(" <> show value <> ")")
    , onComplete: pure unit
    }
  pure unit

-- =============================================================================
-- Test 5: D3 Force Simulation
-- =============================================================================

-- | Type for our simulation nodes
type SimNode = Sim.SimulationNode (label :: String)

setupSimulationTest :: C.Coordinator -> Effect Unit
setupSimulationTest coord = do
  log "Setting up D3 force simulation (8 nodes repelling each other)"

  -- Create simulation
  sim <- Sim.create Sim.defaultConfig

  -- Create nodes starting in a cluster at center
  let nodes :: Array SimNode
      nodes =
        [ { id: 0, x: 200.0, y: 75.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "A" }
        , { id: 1, x: 210.0, y: 80.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "B" }
        , { id: 2, x: 190.0, y: 70.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "C" }
        , { id: 3, x: 205.0, y: 85.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "D" }
        , { id: 4, x: 195.0, y: 65.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "E" }
        , { id: 5, x: 215.0, y: 75.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "F" }
        , { id: 6, x: 185.0, y: 80.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "G" }
        , { id: 7, x: 200.0, y: 90.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label: "H" }
        ]

  Sim.setNodes nodes sim

  -- Add forces: many-body repulsion + center to keep them in view
  Sim.addForce (ManyBody "charge" defaultManyBody { strength = -50.0 }) sim
  Sim.addForce (Center "center" defaultCenter { x = 200.0, y = 75.0 }) sim

  -- Get DOM elements for the simulation nodes
  n0 <- getElementById "node0"
  n1 <- getElementById "node1"
  n2 <- getElementById "node2"
  n3 <- getElementById "node3"
  n4 <- getElementById "node4"
  n5 <- getElementById "node5"
  n6 <- getElementById "node6"
  n7 <- getElementById "node7"
  let nodeElements = [n0, n1, n2, n3, n4, n5, n6, n7]

  -- Register simulation consumer
  -- Note: We use the simulationConsumer which wraps Sim.tick
  _ <- C.register coord
    { tick: simulationConsumer sim 0.001 do
        -- Render: read current positions and update DOM
        currentNodes <- Sim.getNodes sim
        renderNodes nodeElements currentNodes
    , onComplete: log "✓ Force simulation converged!"
    }
  pure unit

renderNodes :: forall r. Array DomElement -> Array (Sim.SimulationNode r) -> Effect Unit
renderNodes elements nodes = go elements nodes
  where
  go es ns = case uncons es, uncons ns of
    Just { head: e, tail: es' }, Just { head: n, tail: ns' } -> do
      setPosition e n.x n.y
      go es' ns'
    _, _ -> pure unit

-- =============================================================================
-- Test 6: WASM Force Simulation
-- =============================================================================

setupWASMSimulationTest :: C.Coordinator -> Effect Unit
setupWASMSimulationTest coord = do
  log "Setting up WASM force simulation (6 nodes repelling each other)"

  -- Create WASM simulation with 6 nodes
  sim <- WASM.createSimulation 6

  -- Set initial positions (clustered at center-right of container)
  let initialPositions =
        [ 350.0, 75.0   -- node 0
        , 360.0, 80.0   -- node 1
        , 340.0, 70.0   -- node 2
        , 355.0, 85.0   -- node 3
        , 345.0, 65.0   -- node 4
        , 365.0, 75.0   -- node 5
        ]
  WASM.setPositions sim initialPositions

  -- Configure forces
  WASM.configureManyBody sim (-50.0) 0.9 1.0 1000.0  -- strength, theta, distMin, distMax
  WASM.configureCenter sim 350.0 75.0 0.1            -- x, y, strength
  WASM.enableForces sim true false true              -- manyBody, links, center

  -- Get DOM elements for WASM nodes
  w0 <- getElementById "wasm0"
  w1 <- getElementById "wasm1"
  w2 <- getElementById "wasm2"
  w3 <- getElementById "wasm3"
  w4 <- getElementById "wasm4"
  w5 <- getElementById "wasm5"
  let wasmElements = [w0, w1, w2, w3, w4, w5]

  -- Register WASM simulation consumer
  _ <- C.register coord
    { tick: wasmConsumer sim 0.001 do
        -- Render: read positions and update DOM
        positions <- WASM.getPositions sim
        renderWASMNodes wasmElements positions
    , onComplete: log "✓ WASM simulation converged!"
    }
  pure unit

-- | Consumer for WASM force simulation
wasmConsumer
  :: WASM.WASMSimulation
  -> Number              -- ^ Alpha threshold for completion
  -> Effect Unit         -- ^ Render callback
  -> C.Milliseconds
  -> Effect C.TickResult
wasmConsumer sim alphaMin onTick _deltaMs = do
  alpha <- WASM.tick sim
  onTick
  pure $ if alpha < alphaMin
    then C.Completed
    else C.Converged alpha

-- | Render WASM nodes from flat position array [x0, y0, x1, y1, ...]
renderWASMNodes :: Array DomElement -> Array Number -> Effect Unit
renderWASMNodes elements positions = go 0 elements
  where
  go i es = case uncons es of
    Nothing -> pure unit
    Just { head: e, tail: rest } -> do
      case positions !! (i * 2), positions !! (i * 2 + 1) of
        Just x, Just y -> setPosition e x y
        _, _ -> pure unit
      go (i + 1) rest
