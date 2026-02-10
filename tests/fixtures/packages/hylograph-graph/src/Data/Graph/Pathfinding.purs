-- | Pathfinding Algorithms
-- |
-- | Pure implementations of graph traversal and shortest path algorithms.
-- |
-- | For visualization-friendly traced variants, see `Data.Graph.Pathfinding.Traced`.
module Data.Graph.Pathfinding
  ( -- * Types
    PathResult(..)
  , SearchResult
    -- * Shortest Path (Weighted)
  , dijkstra
  , shortestPath
  , findPath  -- Alias for shortestPath (backwards compatibility)
    -- * Traversal (Unweighted)
  , bfs
  , dfs
  , bfsFrom
  , dfsFrom
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, minimumBy)
import Data.List (List)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set

import Data.Graph.Types (Graph, NodeId, Path, neighbors)

-- =============================================================================
-- Types
-- =============================================================================

-- | Result of pathfinding between two nodes
data PathResult
  = PathFound { path :: Path, cost :: Number }
  | NoPath
  | SameNode

-- | Result of a graph search from a starting node
-- | Contains distances/depths and parent pointers for path reconstruction
type SearchResult =
  { distances :: Map NodeId Number    -- Distance/depth from start
  , parents :: Map NodeId NodeId      -- Parent in search tree
  , visited :: Array NodeId           -- Nodes in visit order
  }

-- =============================================================================
-- Dijkstra's Algorithm (Weighted Shortest Paths)
-- =============================================================================

-- | Dijkstra's algorithm: find shortest paths from a source to all reachable nodes
-- |
-- | Returns distances and parent pointers for path reconstruction.
-- |
-- | ```purescript
-- | let result = dijkstra (NodeId "A") graph
-- | -- result.distances: Map from each node to its distance from A
-- | -- result.parents: Map from each node to its parent in shortest path tree
-- | ```
dijkstra :: NodeId -> Graph -> SearchResult
dijkstra start graph = search initialState
  where
  initialState :: DijkstraState
  initialState =
    { openSet: Set.singleton start
    , distances: Map.singleton start 0.0
    , parents: Map.empty
    , visited: []
    }

  search :: DijkstraState -> SearchResult
  search state
    | Set.isEmpty state.openSet =
        { distances: state.distances
        , parents: state.parents
        , visited: state.visited
        }
    | otherwise =
        let current = findMinDistance state.openSet state.distances
            openSet' = Set.delete current state.openSet
            visited' = Array.snoc state.visited current
            state' = foldl (relaxNeighbor current)
                       (state { openSet = openSet', visited = visited' })
                       (neighbors current graph)
        in search state'

  findMinDistance :: Set NodeId -> Map NodeId Number -> NodeId
  findMinDistance openSet distances =
    fromMaybe (unsafeHead $ Set.toUnfoldable openSet) $
      minimumBy (comparing (flip getDistance distances))
        (Set.toUnfoldable openSet :: Array NodeId)

  getDistance :: NodeId -> Map NodeId Number -> Number
  getDistance node distances = fromMaybe infinity $ Map.lookup node distances

  relaxNeighbor :: NodeId -> DijkstraState -> { neighbor :: NodeId, weight :: Number } -> DijkstraState
  relaxNeighbor current state { neighbor, weight } =
    let currentDist = getDistance current state.distances
        newDist = currentDist + weight
        oldDist = getDistance neighbor state.distances
    in if newDist < oldDist
       then state
              { openSet = Set.insert neighbor state.openSet
              , distances = Map.insert neighbor newDist state.distances
              , parents = Map.insert neighbor current state.parents
              }
       else state

type DijkstraState =
  { openSet :: Set NodeId
  , distances :: Map NodeId Number
  , parents :: Map NodeId NodeId
  , visited :: Array NodeId
  }

-- | Find shortest path between two nodes using Dijkstra's algorithm
-- |
-- | This is the main pathfinding function for weighted graphs.
shortestPath :: NodeId -> NodeId -> Graph -> PathResult
shortestPath start goal graph
  | start == goal = SameNode
  | otherwise =
      let result = dijkstraTo start goal graph
      in case Map.lookup goal result.distances of
           Nothing -> NoPath
           Just cost -> PathFound
             { path: reconstructPath result.parents start goal
             , cost
             }

-- | Dijkstra with early termination when goal is reached
dijkstraTo :: NodeId -> NodeId -> Graph -> SearchResult
dijkstraTo start goal graph = search initialState
  where
  initialState =
    { openSet: Set.singleton start
    , distances: Map.singleton start 0.0
    , parents: Map.empty
    , visited: []
    }

  search :: DijkstraState -> SearchResult
  search state
    | Set.isEmpty state.openSet = toResult state
    | otherwise =
        let current = findMinDistance state.openSet state.distances
        in if current == goal
           then toResult (state { visited = Array.snoc state.visited current })
           else
             let openSet' = Set.delete current state.openSet
                 visited' = Array.snoc state.visited current
                 state' = foldl (relaxNeighbor current)
                            (state { openSet = openSet', visited = visited' })
                            (neighbors current graph)
             in search state'

  findMinDistance openSet distances =
    fromMaybe (unsafeHead $ Set.toUnfoldable openSet) $
      minimumBy (comparing (flip getDistance distances))
        (Set.toUnfoldable openSet :: Array NodeId)

  getDistance node distances = fromMaybe infinity $ Map.lookup node distances

  relaxNeighbor current state { neighbor, weight } =
    let currentDist = getDistance current state.distances
        newDist = currentDist + weight
        oldDist = getDistance neighbor state.distances
    in if newDist < oldDist
       then state
              { openSet = Set.insert neighbor state.openSet
              , distances = Map.insert neighbor newDist state.distances
              , parents = Map.insert neighbor current state.parents
              }
       else state

  toResult state =
    { distances: state.distances
    , parents: state.parents
    , visited: state.visited
    }

-- =============================================================================
-- Breadth-First Search (Unweighted)
-- =============================================================================

-- | BFS from a starting node
-- |
-- | Returns all reachable nodes with their depths and parent pointers.
-- | Useful for unweighted shortest paths.
bfs :: NodeId -> Graph -> SearchResult
bfs start graph = search initialState (List.singleton start)
  where
  initialState =
    { distances: Map.singleton start 0.0
    , parents: Map.empty
    , visited: []
    }

  search :: BFSState -> List NodeId -> SearchResult
  search state List.Nil =
    { distances: state.distances
    , parents: state.parents
    , visited: state.visited
    }
  search state queue =
    case List.uncons queue of
      Nothing ->
        { distances: state.distances
        , parents: state.parents
        , visited: state.visited
        }
      Just { head: current, tail: rest } ->
        if Array.elem current state.visited
        then search state rest
        else
          let visited' = Array.snoc state.visited current
              currentDepth = fromMaybe 0.0 $ Map.lookup current state.distances
              neighborNodes = neighbors current graph
              unvisited = Array.filter (\n -> not (Map.member n.neighbor state.distances)) neighborNodes
              newQueue = rest <> List.fromFoldable (map _.neighbor unvisited)
              newDistances = foldl (\m n -> Map.insert n.neighbor (currentDepth + 1.0) m)
                               state.distances unvisited
              newParents = foldl (\m n -> Map.insert n.neighbor current m)
                             state.parents unvisited
          in search { distances: newDistances, parents: newParents, visited: visited' } newQueue

type BFSState =
  { distances :: Map NodeId Number
  , parents :: Map NodeId NodeId
  , visited :: Array NodeId
  }

-- | BFS returning just the nodes in visit order
bfsFrom :: NodeId -> Graph -> Array NodeId
bfsFrom start graph = (bfs start graph).visited

-- =============================================================================
-- Depth-First Search
-- =============================================================================

-- | DFS from a starting node
-- |
-- | Returns all reachable nodes with discovery times and parent pointers.
dfs :: NodeId -> Graph -> SearchResult
dfs start graph =
  let result = search { distances: Map.empty, parents: Map.empty, visited: [], time: 0.0 } start
  in { distances: result.distances, parents: result.parents, visited: result.visited }
  where
  search :: DFSState -> NodeId -> DFSState
  search state node
    | Map.member node state.distances = state  -- Already visited
    | otherwise =
        let time' = state.time + 1.0
            state' = state
              { distances = Map.insert node time' state.distances
              , visited = Array.snoc state.visited node
              , time = time'
              }
            neighborNodes = neighbors node graph
        in foldl (\s n ->
             if Map.member n.neighbor s.distances
             then s
             else search (s { parents = Map.insert n.neighbor node s.parents }) n.neighbor
           ) state' neighborNodes

type DFSState =
  { distances :: Map NodeId Number  -- Discovery time
  , parents :: Map NodeId NodeId
  , visited :: Array NodeId
  , time :: Number
  }

-- | DFS returning just the nodes in visit order
dfsFrom :: NodeId -> Graph -> Array NodeId
dfsFrom start graph = (dfs start graph).visited

-- =============================================================================
-- Helpers
-- =============================================================================

infinity :: Number
infinity = 1.0e308

-- | Reconstruct path from parent pointers
reconstructPath :: Map NodeId NodeId -> NodeId -> NodeId -> Path
reconstructPath parents start goal = go [goal] goal
  where
  go path node
    | node == start = path
    | otherwise = case Map.lookup node parents of
        Nothing -> path  -- Shouldn't happen if goal was reachable
        Just parent -> go (Array.cons parent path) parent

-- | Unsafe head (only used when we know array is non-empty)
unsafeHead :: forall a. Array a -> a
unsafeHead arr = case Array.head arr of
  Just x -> x
  Nothing -> unsafeHead arr

-- | Alias for shortestPath (backwards compatibility with A* demo)
findPath :: NodeId -> NodeId -> Graph -> PathResult
findPath = shortestPath
