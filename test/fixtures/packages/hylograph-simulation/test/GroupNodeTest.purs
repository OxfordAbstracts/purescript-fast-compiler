-- | Group Node Test
-- |
-- | Tests the runSimulation API with different force configurations.
-- | Note: Rendering is now handled externally (via HATS or any other approach).
-- | This test focuses on the simulation physics and event model.
module Test.GroupNodeTest where

import Prelude

import Data.Nullable (null) as Nullable
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Console (log)
import Effect.Exception (try, message)

-- The high-level API
import Hylograph.Simulation
  ( runSimulation
  , Engine(..)
  , SimulationNode
  , SimulationEvent(..)
  , subscribe
  , setup
  , manyBody
  , collide
  , positionX
  , center
  , withStrength
  , withRadius
  , withX
  , withY
  , static
  , dynamic
  )

-- =============================================================================
-- Node Type
-- =============================================================================

-- | Node with a radius for collision
type MyNode = SimulationNode (r :: Number, color :: String)

-- =============================================================================
-- Main
-- =============================================================================

main :: Effect Unit
main = do
  log "Group Node Test Starting..."

  -- Test 1: manyBody + center forces
  log "Test 1: manyBody + center forces..."
  result1 <- runSimulation
    { engine: D3
    , setup: setup "test1"
        [ manyBody "charge" # withStrength (static (-50.0))
        , center "center" # withX (static 200.0) # withY (static 100.0)
        ]
    , nodes: testNodes 200.0
    , links: []
    , container: "#test1"
    , alphaMin: 0.001
    }

  _ <- subscribe result1.events \event -> case event of
    Completed -> log "✓ Test 1: manyBody + center completed!"
    _ -> pure unit

  -- Test 2: Simple manyBody + center
  log "Test 2: Simple manyBody + center..."
  result2E <- try $ runSimulation
    { engine: D3
    , setup: setup "test2"
        [ manyBody "charge" # withStrength (static (-50.0))
        , center "center" # withX (static 150.0) # withY (static 100.0)
        ]
    , nodes: testNodes 150.0
    , links: []
    , container: "#test2"
    , alphaMin: 0.001
    }

  case result2E of
    Left err -> log $ "ERROR Test 2: " <> message err
    Right result2 -> do
      log "Test 2 simulation created"
      _ <- subscribe result2.events \event -> case event of
        Completed -> log "✓ Test 2: Simple forces completed!"
        _ -> pure unit
      pure unit

  -- Test 3: positionX with dynamic target (like beeswarm)
  log "Test 3: positionX with dynamic target..."
  result3E <- try $ runSimulation
    { engine: D3
    , setup: setup "test3"
        [ positionX "x" # withX (dynamic _.targetX) # withStrength (static 0.1)
        , collide "collision" # withRadius (dynamic \n -> n.r + 2.0) # withStrength (static 1.0)
        ]
    , nodes: testNodesWithTarget
    , links: []
    , container: "#test3"
    , alphaMin: 0.001
    }

  case result3E of
    Left err -> log $ "ERROR Test 3: " <> message err
    Right result3 -> do
      log "Test 3 simulation created"
      _ <- subscribe result3.events \event -> case event of
        Completed -> log "✓ Test 3: Dynamic positionX completed!"
        _ -> pure unit
      pure unit

  log "All tests started! Watch for completion messages."

-- =============================================================================
-- Test Data
-- =============================================================================

testNodes :: Number -> Array MyNode
testNodes centerX =
  [ mkNode 0 (centerX + 0.0) 100.0 10.0 "#e63946"
  , mkNode 1 (centerX + 20.0) 120.0 8.0 "#f4a261"
  , mkNode 2 (centerX - 20.0) 80.0 12.0 "#2a9d8f"
  , mkNode 3 (centerX + 30.0) 110.0 6.0 "#264653"
  , mkNode 4 (centerX - 30.0) 90.0 14.0 "#e9c46a"
  , mkNode 5 (centerX + 10.0) 130.0 9.0 "#457b9d"
  ]

-- Nodes with different target X positions (like beeswarm layers)
testNodesWithTarget :: Array (SimulationNode (r :: Number, color :: String, targetX :: Number))
testNodesWithTarget =
  [ { id: 0, x: 150.0, y: 100.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, r: 10.0, color: "#e63946", targetX: 75.0 }
  , { id: 1, x: 150.0, y: 100.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, r: 8.0, color: "#f4a261", targetX: 75.0 }
  , { id: 2, x: 150.0, y: 100.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, r: 12.0, color: "#2a9d8f", targetX: 150.0 }
  , { id: 3, x: 150.0, y: 100.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, r: 6.0, color: "#264653", targetX: 150.0 }
  , { id: 4, x: 150.0, y: 100.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, r: 14.0, color: "#e9c46a", targetX: 225.0 }
  , { id: 5, x: 150.0, y: 100.0, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, r: 9.0, color: "#457b9d", targetX: 225.0 }
  ]

mkNode :: Int -> Number -> Number -> Number -> String -> MyNode
mkNode id x y r color =
  { id, x, y, vx: 0.0, vy: 0.0, fx: Nullable.null, fy: Nullable.null, r, color }
