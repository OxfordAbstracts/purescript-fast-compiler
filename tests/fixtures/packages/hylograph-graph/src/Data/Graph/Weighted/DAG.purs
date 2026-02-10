-- | Data.Graph.Weighted.DAG
-- |
-- | Directed Acyclic Graph (DAG) as a newtype over WeightedDigraph.
-- | Provides a smart constructor that validates acyclicity and
-- | DAG-specific algorithms like topological sort and layer computation.
module Data.Graph.Weighted.DAG
  ( DAG
  , DAGError(..)
  , fromWeightedDigraph
  , unsafeFromWeightedDigraph
  , unsafeAddEdge
  , toWeightedDigraph
  , topologicalSort
  , depths
  , heights
  , layers
  , sources
  , sinks
  , nodes
  , edges
  , outgoing
  , incoming
  , nodeCount
  , edgeCount
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Graph.Algorithms (findCycle)
import Data.Graph.Weighted (WeightedDigraph, WeightedEdge)
import Data.Graph.Weighted as WG
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))

-- | A Directed Acyclic Graph (DAG) wrapping a WeightedDigraph.
-- |
-- | The smart constructor `fromWeightedDigraph` guarantees acyclicity.
-- | Use `unsafeFromWeightedDigraph` only when you know the input is acyclic.
newtype DAG node weight = DAG (WeightedDigraph node weight)

-- | Error when attempting to create a DAG from a cyclic graph
data DAGError node = CycleDetected (Array node)

derive instance eqDAGError :: Eq node => Eq (DAGError node)

instance showDAGError :: Show node => Show (DAGError node) where
  show (CycleDetected cycle) = "CycleDetected " <> show cycle

-- | Create a DAG from a WeightedDigraph, validating that it's acyclic.
-- |
-- | Returns `Left (CycleDetected nodes)` if a cycle is found.
fromWeightedDigraph :: forall node weight. Ord node => WeightedDigraph node weight -> Either (DAGError node) (DAG node weight)
fromWeightedDigraph g =
  let simpleGraph = WG.toSimpleGraph g
  in case findCycle simpleGraph of
    Just cycle -> Left (CycleDetected cycle)
    Nothing -> Right (DAG g)

-- | Create a DAG without validation.
-- |
-- | **Warning**: Only use this when you know the input is acyclic.
-- | Using this with a cyclic graph will cause infinite loops in
-- | algorithms like `topologicalSort` and `depths`.
unsafeFromWeightedDigraph :: forall node weight. WeightedDigraph node weight -> DAG node weight
unsafeFromWeightedDigraph = DAG

-- | Extract the underlying WeightedDigraph
toWeightedDigraph :: forall node weight. DAG node weight -> WeightedDigraph node weight
toWeightedDigraph (DAG g) = g

-- | Add an edge to the DAG without cycle validation.
-- |
-- | **Warning**: Only use this when you know the edge won't create a cycle.
-- | This is useful for incremental building when you trust the input is acyclic.
unsafeAddEdge :: forall node weight. Ord node => node -> node -> weight -> DAG node weight -> DAG node weight
unsafeAddEdge source target weight (DAG g) = DAG (WG.addEdge source target weight g)

-- | Get source nodes (nodes with no incoming edges)
sources :: forall node weight. Ord node => DAG node weight -> Array node
sources (DAG g) = WG.sources g

-- | Get sink nodes (nodes with no outgoing edges)
sinks :: forall node weight. Ord node => DAG node weight -> Array node
sinks (DAG g) = WG.sinks g

-- | Get all nodes
nodes :: forall node weight. DAG node weight -> Array node
nodes (DAG g) = WG.nodes g

-- | Get all edges
edges :: forall node weight. DAG node weight -> Array (WeightedEdge node weight)
edges (DAG g) = WG.edges g

-- | Get outgoing edges from a node
outgoing :: forall node weight. Ord node => node -> DAG node weight -> Array { target :: node, weight :: weight }
outgoing node (DAG g) = WG.outgoing node g

-- | Get incoming edges to a node
incoming :: forall node weight. Ord node => node -> DAG node weight -> Array { source :: node, weight :: weight }
incoming node (DAG g) = WG.incoming node g

-- | Get the number of nodes
nodeCount :: forall node weight. DAG node weight -> Int
nodeCount (DAG g) = WG.nodeCount g

-- | Get the number of edges
edgeCount :: forall node weight. DAG node weight -> Int
edgeCount (DAG g) = WG.edgeCount g

-- | Compute topological sort using Kahn's algorithm.
-- |
-- | Returns nodes in dependency order (sources first, sinks last).
-- | Since we've validated acyclicity, this always succeeds.
topologicalSort :: forall node weight. Ord node => DAG node weight -> Array node
topologicalSort dag@(DAG g) =
  let
    -- Start with all source nodes
    initialQueue = sources dag

    -- Track in-degrees
    initialInDegrees = foldl (\acc n ->
      Map.insert n (Array.length $ WG.incoming n g) acc
    ) Map.empty (WG.nodes g)

    -- Kahn's algorithm
    go :: Array node -> Array node -> Map node Int -> Array node
    go result queue inDegrees
      | Array.null queue = result
      | otherwise =
          case Array.uncons queue of
            Nothing -> result
            Just { head: current, tail: rest } ->
              let
                -- Get targets of current node
                targets = map _.target $ WG.outgoing current g

                -- Decrement in-degrees and collect newly ready nodes
                { newInDegrees, newReady } = foldl
                  (\acc target ->
                    let
                      oldDeg = fromMaybe 0 $ Map.lookup target acc.newInDegrees
                      newDeg = oldDeg - 1
                    in
                      { newInDegrees: Map.insert target newDeg acc.newInDegrees
                      , newReady: if newDeg == 0
                                  then Array.snoc acc.newReady target
                                  else acc.newReady
                      }
                  )
                  { newInDegrees: inDegrees, newReady: [] }
                  targets
              in
                go (Array.snoc result current) (rest <> newReady) newInDegrees
  in
    go [] initialQueue initialInDegrees

-- | Compute depth (distance from sources) for each node using BFS.
-- |
-- | Source nodes have depth 0. Each node's depth is 1 + max depth of its predecessors.
-- | This is the "left-to-right" distance in Sankey terminology.
depths :: forall node weight. Ord node => DAG node weight -> Map node Int
depths dag@(DAG g) =
  let
    -- Start BFS from sources at depth 0
    sourceNodes = sources dag
    initialDepths = Map.fromFoldable $ map (\n -> Tuple n 0) sourceNodes
    initialFrontier = Set.fromFoldable sourceNodes
  in
    bfs initialDepths initialFrontier 0
  where
    bfs :: Map node Int -> Set node -> Int -> Map node Int
    bfs depthMap frontier currentDepth
      | Set.isEmpty frontier = depthMap
      | otherwise =
          let
            -- Get all targets of frontier nodes
            nextNodes = foldl
              (\acc n ->
                let targets = map _.target $ WG.outgoing n g
                in Set.union acc (Set.fromFoldable targets)
              )
              Set.empty
              (Set.toUnfoldable frontier :: Array node)

            -- Filter to only nodes we haven't assigned a depth to yet
            newFrontier = Set.filter (\n -> not $ Map.member n depthMap) nextNodes

            -- Assign depth to new frontier nodes
            nextDepth = currentDepth + 1
            newDepthMap = foldl
              (\acc n -> Map.insert n nextDepth acc)
              depthMap
              (Set.toUnfoldable newFrontier :: Array node)
          in
            bfs newDepthMap newFrontier nextDepth

-- | Compute height (distance from sinks) for each node using reverse BFS.
-- |
-- | Sink nodes have height 0. Each node's height is 1 + max height of its successors.
-- | This is the "right-to-left" distance in Sankey terminology.
heights :: forall node weight. Ord node => DAG node weight -> Map node Int
heights dag@(DAG g) =
  let
    -- Start BFS from sinks at height 0
    sinkNodes = sinks dag
    initialHeights = Map.fromFoldable $ map (\n -> Tuple n 0) sinkNodes
    initialFrontier = Set.fromFoldable sinkNodes
  in
    bfs initialHeights initialFrontier 0
  where
    bfs :: Map node Int -> Set node -> Int -> Map node Int
    bfs heightMap frontier currentHeight
      | Set.isEmpty frontier = heightMap
      | otherwise =
          let
            -- Get all sources of frontier nodes (reverse direction)
            nextNodes = foldl
              (\acc n ->
                let srcs = map _.source $ WG.incoming n g
                in Set.union acc (Set.fromFoldable srcs)
              )
              Set.empty
              (Set.toUnfoldable frontier :: Array node)

            -- Filter to only nodes we haven't assigned a height to yet
            newFrontier = Set.filter (\n -> not $ Map.member n heightMap) nextNodes

            -- Assign height to new frontier nodes
            nextHeight = currentHeight + 1
            newHeightMap = foldl
              (\acc n -> Map.insert n nextHeight acc)
              heightMap
              (Set.toUnfoldable newFrontier :: Array node)
          in
            bfs newHeightMap newFrontier nextHeight

-- | Compute layer assignment for each node.
-- |
-- | Uses depth as the primary layer (same as Sankey's "Justify" alignment).
-- | This groups nodes that can be processed in parallel.
layers :: forall node weight. Ord node => DAG node weight -> Map node Int
layers = depths
