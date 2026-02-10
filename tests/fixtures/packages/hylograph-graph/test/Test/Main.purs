module Test.Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Graph.Weighted as WG
import Data.Graph.Weighted.DAG (DAGError(..))
import Data.Graph.Weighted.DAG as DAG
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

-- Simple test utilities
assert :: String -> Boolean -> Effect Unit
assert name condition =
  if condition
    then log $ "  PASS: " <> name
    else log $ "  FAIL: " <> name

assertEq :: forall a. Eq a => Show a => String -> a -> a -> Effect Unit
assertEq name expected actual =
  if expected == actual
    then log $ "  PASS: " <> name
    else log $ "  FAIL: " <> name <> " - expected " <> show expected <> ", got " <> show actual

-- Test data: A simple flow network
--     A --10--> B --5--> D
--      \               /
--       --3--> C --7--/
--
simpleFlowEdges :: Array { source :: String, target :: String, weight :: Number }
simpleFlowEdges =
  [ { source: "A", target: "B", weight: 10.0 }
  , { source: "A", target: "C", weight: 3.0 }
  , { source: "B", target: "D", weight: 5.0 }
  , { source: "C", target: "D", weight: 7.0 }
  ]

-- Linear chain: A -> B -> C -> D
linearChainEdges :: Array { source :: String, target :: String, weight :: Number }
linearChainEdges =
  [ { source: "A", target: "B", weight: 1.0 }
  , { source: "B", target: "C", weight: 1.0 }
  , { source: "C", target: "D", weight: 1.0 }
  ]

-- Graph with a cycle: A -> B -> C -> A
cyclicEdges :: Array { source :: String, target :: String, weight :: Number }
cyclicEdges =
  [ { source: "A", target: "B", weight: 1.0 }
  , { source: "B", target: "C", weight: 1.0 }
  , { source: "C", target: "A", weight: 1.0 }
  ]

main :: Effect Unit
main = do
  log "=== WeightedDigraph Tests ==="
  testWeightedDigraph
  log ""
  log "=== DAG Tests ==="
  testDAG
  log ""
  log "=== All tests completed ==="

testWeightedDigraph :: Effect Unit
testWeightedDigraph = do
  let graph = WG.fromEdges simpleFlowEdges

  log "Building graph from edges:"
  assertEq "node count" 4 (WG.nodeCount graph)
  assertEq "edge count" 4 (WG.edgeCount graph)

  log "Node membership:"
  assert "has node A" (WG.hasNode "A" graph)
  assert "has node D" (WG.hasNode "D" graph)
  assert "doesn't have node X" (not $ WG.hasNode "X" graph)

  log "Edge existence:"
  assert "has edge A->B" (WG.hasEdge "A" "B" graph)
  assert "has edge C->D" (WG.hasEdge "C" "D" graph)
  assert "doesn't have edge B->A (directed)" (not $ WG.hasEdge "B" "A" graph)

  log "Outgoing edges:"
  let outA = WG.outgoing "A" graph
  assertEq "A has 2 outgoing edges" 2 (Array.length outA)

  log "Incoming edges:"
  let inD = WG.incoming "D" graph
  assertEq "D has 2 incoming edges" 2 (Array.length inD)

  log "Sources and sinks:"
  let srcs = WG.sources graph
  let snks = WG.sinks graph
  assertEq "sources" ["A"] srcs
  assertEq "sinks" ["D"] snks

testDAG :: Effect Unit
testDAG = do
  log "Smart constructor validation:"

  -- Valid DAG
  let validGraph = WG.fromEdges simpleFlowEdges
  case DAG.fromWeightedDigraph validGraph of
    Right _ -> log "  PASS: accepts valid DAG"
    Left err -> log $ "  FAIL: rejected valid DAG with " <> show err

  -- Cyclic graph should be rejected
  let cyclicGraph = WG.fromEdges cyclicEdges
  case DAG.fromWeightedDigraph cyclicGraph of
    Left (CycleDetected _) -> log "  PASS: rejects cyclic graph"
    Right _ -> log "  FAIL: accepted cyclic graph"

  log "DAG operations (using simple flow network):"
  let dag = DAG.unsafeFromWeightedDigraph validGraph

  -- Sources and sinks
  assertEq "DAG sources" ["A"] (DAG.sources dag)
  assertEq "DAG sinks" ["D"] (DAG.sinks dag)

  log "Topological sort:"
  let topo = DAG.topologicalSort dag
  -- A must come before B and C, B and C must come before D
  let aIdx = Array.findIndex (_ == "A") topo
  let bIdx = Array.findIndex (_ == "B") topo
  let cIdx = Array.findIndex (_ == "C") topo
  let dIdx = Array.findIndex (_ == "D") topo
  case aIdx, bIdx, cIdx, dIdx of
    Just ai, Just bi, Just ci, Just di -> do
      assert "A before B" (ai < bi)
      assert "A before C" (ai < ci)
      assert "B before D" (bi < di)
      assert "C before D" (ci < di)
    _, _, _, _ -> log "  FAIL: missing nodes in topological sort"

  log "Depth computation (linear chain):"
  let linearGraph = WG.fromEdges linearChainEdges
  let linearDag = DAG.unsafeFromWeightedDigraph linearGraph
  let depthMap = DAG.depths linearDag
  assertEq "A depth" (Just 0) (Map.lookup "A" depthMap)
  assertEq "B depth" (Just 1) (Map.lookup "B" depthMap)
  assertEq "C depth" (Just 2) (Map.lookup "C" depthMap)
  assertEq "D depth" (Just 3) (Map.lookup "D" depthMap)

  log "Height computation (linear chain):"
  let heightMap = DAG.heights linearDag
  assertEq "A height" (Just 3) (Map.lookup "A" heightMap)
  assertEq "B height" (Just 2) (Map.lookup "B" heightMap)
  assertEq "C height" (Just 1) (Map.lookup "C" heightMap)
  assertEq "D height" (Just 0) (Map.lookup "D" heightMap)

  log "Depths on flow network:"
  let flowDepths = DAG.depths dag
  assertEq "A depth (flow)" (Just 0) (Map.lookup "A" flowDepths)
  assertEq "B depth (flow)" (Just 1) (Map.lookup "B" flowDepths)
  assertEq "C depth (flow)" (Just 1) (Map.lookup "C" flowDepths)
  assertEq "D depth (flow)" (Just 2) (Map.lookup "D" flowDepths)
