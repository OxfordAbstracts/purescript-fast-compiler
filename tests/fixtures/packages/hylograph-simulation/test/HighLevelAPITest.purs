-- | High-Level API Test
-- |
-- | Demonstrates the simplified runSimulation API with unified event emitter.
-- | This is how users should typically interact with the library.
-- |
-- | The same event model works for both D3 and WASM engines, and can be
-- | adapted to any UI framework (Halogen, React, vanilla JS).
-- |
-- | Note: Rendering is now handled externally (via HATS or any other approach).
-- | This test focuses on the simulation physics and event model.
module Test.HighLevelAPITest where

import Prelude

import Data.Nullable (null) as Nullable
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)
import Effect.Exception (try, message)
import Data.Either (Either(..))

-- The high-level API - just one import!
import Hylograph.Simulation
  ( runSimulation
  , initWASM
  , Engine(..)
  , SimulationNode
  , SimulationEvent(..)
  , subscribe
  , setup
  , manyBody
  , center
  , withStrength
  , withX
  , withY
  , static
  )

-- =============================================================================
-- Node Type
-- =============================================================================

-- | Concrete node type
-- | Note: Records have automatic Ord instances when all fields are Ord
type MyNode = SimulationNode (label :: String)

-- =============================================================================
-- Main
-- =============================================================================

main :: Effect Unit
main = launchAff_ do
  liftEffect $ log "High-Level API Test Starting..."

  -- Initialize WASM (call once at app startup)
  liftEffect $ log "Initializing WASM..."
  initWASM "./wasm-pkg/force_kernel.js"
  liftEffect $ log "WASM initialized!"

  liftEffect do
    -- D3 Simulation - returns handle AND event emitter
    log "Starting D3 simulation..."
    d3Result <- try $ runSimulation
      { engine: D3
      , setup: setup "physics"
          [ manyBody "charge" # withStrength (static (-80.0))
          , center "center" # withX (static 150.0) # withY (static 75.0)
          ]
      , nodes: initialNodes 150.0
      , links: []
      , container: "#d3-sim"
      , alphaMin: 0.001
      }

    case d3Result of
      Left err -> log $ "D3 simulation ERROR: " <> message err
      Right { handle: d3Handle, events: d3Events } -> do
        log "D3 simulation created successfully"
        -- Subscribe to D3 events (framework-agnostic!)
        -- In real usage, you'd render nodes on Tick using handle.getNodes
        _ <- subscribe d3Events \event -> case event of
          Tick _ -> do
            -- Could render here: nodes <- d3Handle.getNodes; renderNodes(nodes)
            pure unit
          Completed -> log "✓ D3 simulation converged!"
          _ -> pure unit
        pure unit

    -- WASM Simulation - same API, same event model!
    log "Starting WASM simulation..."
    wasmResult <- try $ runSimulation
      { engine: WASM
      , setup: setup "physics"
          [ manyBody "charge" # withStrength (static (-80.0))
          , center "center" # withX (static 350.0) # withY (static 75.0)
          ]
      , nodes: initialNodes 350.0
      , links: []
      , container: "#wasm-sim"
      , alphaMin: 0.001
      }

    case wasmResult of
      Left err -> log $ "WASM simulation ERROR: " <> message err
      Right { handle: wasmHandle, events: wasmEvents } -> do
        log "WASM simulation created successfully"
        -- Subscribe to WASM events (identical pattern!)
        _ <- subscribe wasmEvents \event -> case event of
          Tick _ -> do
            -- Could render here: nodes <- wasmHandle.getNodes; renderNodes(nodes)
            pure unit
          Completed -> log "✓ WASM simulation converged!"
          _ -> pure unit
        pure unit

    log "Both simulations running with unified event model!"

    -- Later: could update data
    -- result <- d3Handle.updateData newNodes []
    -- log $ "Entered: " <> show (length result.nodes.entered)

-- =============================================================================
-- Helpers
-- =============================================================================

-- | Create initial nodes centered around a point
initialNodes :: Number -> Array MyNode
initialNodes centerX =
  [ mkNode 0 (centerX + 0.0) 75.0 "A"
  , mkNode 1 (centerX + 10.0) 80.0 "B"
  , mkNode 2 (centerX - 10.0) 70.0 "C"
  , mkNode 3 (centerX + 5.0) 85.0 "D"
  , mkNode 4 (centerX - 5.0) 65.0 "E"
  , mkNode 5 (centerX + 15.0) 75.0 "F"
  ]

mkNode :: Int -> Number -> Number -> String -> MyNode
mkNode id x y label =
  { id, x, y, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, label }
