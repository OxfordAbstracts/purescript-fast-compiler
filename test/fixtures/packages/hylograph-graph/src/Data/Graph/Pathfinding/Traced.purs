-- | Traced Pathfinding Algorithms
-- |
-- | Visualization-friendly variants that record each step of the algorithm.
-- | Use these when you want to animate or visualize the search process.
-- |
-- | ```purescript
-- | import Data.Graph.Pathfinding.Traced (shortestPathTraced, SearchStep(..))
-- |
-- | let traced = shortestPathTraced start goal graph
-- | -- traced.result: the PathResult
-- | -- traced.steps: Array of SearchStep for animation
-- | ```
module Data.Graph.Pathfinding.Traced
  ( -- * Types
    TracedResult
  , SearchStep(..)
    -- * Traced Algorithms
  , shortestPathTraced
  , dijkstraTraced
  , bfsTraced
  , dfsTraced
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, minimumBy)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set

import Data.Graph.Types (Graph, NodeId, Path, neighbors)
import Data.Graph.Pathfinding (PathResult(..), SearchResult)

-- =============================================================================
-- Types
-- =============================================================================

-- | A step in the search algorithm, useful for visualization/animation
data SearchStep
  = Visit NodeId                           -- ^ Currently visiting this node
  | Explore NodeId NodeId Number           -- ^ Exploring edge from -> to with cost/depth
  | UpdateDistance NodeId Number           -- ^ Updated distance to node
  | Backtrack NodeId                       -- ^ Backtracking from this node (DFS)
  | FoundGoal NodeId                       -- ^ Goal reached!

derive instance eqSearchStep :: Eq SearchStep

instance showSearchStep :: Show SearchStep where
  show (Visit n) = "Visit " <> show n
  show (Explore from to cost) = "Explore " <> show from <> " -> " <> show to <> " (" <> show cost <> ")"
  show (UpdateDistance n d) = "UpdateDistance " <> show n <> " = " <> show d
  show (Backtrack n) = "Backtrack " <> show n
  show (FoundGoal n) = "FoundGoal " <> show n

-- | Result of a traced algorithm
-- | Includes both the final result and the steps taken to get there
type TracedResult a =
  { result :: a
  , steps :: Array SearchStep
  , explored :: Set NodeId         -- All nodes that were visited
  }

-- =============================================================================
-- Traced Dijkstra
-- =============================================================================

-- | Dijkstra's algorithm with step-by-step tracing
dijkstraTraced :: NodeId -> Graph -> TracedResult SearchResult
dijkstraTraced start graph = search initialState
  where
  initialState :: TracedDijkstraState
  initialState =
    { openSet: Set.singleton start
    , distances: Map.singleton start 0.0
    , parents: Map.empty
    , visited: []
    , steps: []
    }

  search :: TracedDijkstraState -> TracedResult SearchResult
  search state
    | Set.isEmpty state.openSet =
        { result:
            { distances: state.distances
            , parents: state.parents
            , visited: state.visited
            }
        , steps: state.steps
        , explored: Set.fromFoldable state.visited
        }
    | otherwise =
        let current = findMinDistance state.openSet state.distances
            openSet' = Set.delete current state.openSet
            visited' = Array.snoc state.visited current
            steps' = Array.snoc state.steps (Visit current)
            state' = foldl (relaxNeighborTraced current)
                       (state { openSet = openSet', visited = visited', steps = steps' })
                       (neighbors current graph)
        in search state'

  findMinDistance openSet distances =
    fromMaybe (unsafeHead $ Set.toUnfoldable openSet) $
      minimumBy (comparing (flip getDistance distances))
        (Set.toUnfoldable openSet :: Array NodeId)

  getDistance node distances = fromMaybe infinity $ Map.lookup node distances

  relaxNeighborTraced current state { neighbor, weight } =
    let currentDist = getDistance current state.distances
        newDist = currentDist + weight
        oldDist = getDistance neighbor state.distances
        exploreStep = Explore current neighbor weight
    in if newDist < oldDist
       then state
              { openSet = Set.insert neighbor state.openSet
              , distances = Map.insert neighbor newDist state.distances
              , parents = Map.insert neighbor current state.parents
              , steps = state.steps <> [exploreStep, UpdateDistance neighbor newDist]
              }
       else state { steps = Array.snoc state.steps exploreStep }

type TracedDijkstraState =
  { openSet :: Set NodeId
  , distances :: Map NodeId Number
  , parents :: Map NodeId NodeId
  , visited :: Array NodeId
  , steps :: Array SearchStep
  }

-- | Find shortest path with tracing
shortestPathTraced :: NodeId -> NodeId -> Graph -> TracedResult PathResult
shortestPathTraced start goal graph
  | start == goal =
      { result: SameNode
      , steps: []
      , explored: Set.singleton start
      }
  | otherwise =
      let traced = dijkstraToTraced start goal graph
      in case Map.lookup goal traced.result.distances of
           Nothing ->
             { result: NoPath
             , steps: traced.steps
             , explored: traced.explored
             }
           Just cost ->
             { result: PathFound
                 { path: reconstructPath traced.result.parents start goal
                 , cost
                 }
             , steps: traced.steps <> [FoundGoal goal]
             , explored: traced.explored
             }

-- | Dijkstra with early termination and tracing
dijkstraToTraced :: NodeId -> NodeId -> Graph -> TracedResult SearchResult
dijkstraToTraced start goal graph = search initialState
  where
  initialState =
    { openSet: Set.singleton start
    , distances: Map.singleton start 0.0
    , parents: Map.empty
    , visited: []
    , steps: []
    }

  search state
    | Set.isEmpty state.openSet = toResult state
    | otherwise =
        let current = findMinDistance state.openSet state.distances
            visitStep = Visit current
        in if current == goal
           then toResult (state
                  { visited = Array.snoc state.visited current
                  , steps = Array.snoc state.steps visitStep
                  })
           else
             let openSet' = Set.delete current state.openSet
                 visited' = Array.snoc state.visited current
                 steps' = Array.snoc state.steps visitStep
                 state' = foldl (relaxNeighborTraced current)
                            (state { openSet = openSet', visited = visited', steps = steps' })
                            (neighbors current graph)
             in search state'

  findMinDistance openSet distances =
    fromMaybe (unsafeHead $ Set.toUnfoldable openSet) $
      minimumBy (comparing (flip getDistance distances))
        (Set.toUnfoldable openSet :: Array NodeId)

  getDistance node distances = fromMaybe infinity $ Map.lookup node distances

  relaxNeighborTraced current state { neighbor, weight } =
    let currentDist = getDistance current state.distances
        newDist = currentDist + weight
        oldDist = getDistance neighbor state.distances
        exploreStep = Explore current neighbor weight
    in if newDist < oldDist
       then state
              { openSet = Set.insert neighbor state.openSet
              , distances = Map.insert neighbor newDist state.distances
              , parents = Map.insert neighbor current state.parents
              , steps = state.steps <> [exploreStep, UpdateDistance neighbor newDist]
              }
       else state { steps = Array.snoc state.steps exploreStep }

  toResult state =
    { result:
        { distances: state.distances
        , parents: state.parents
        , visited: state.visited
        }
    , steps: state.steps
    , explored: Set.fromFoldable state.visited
    }

-- =============================================================================
-- Traced BFS
-- =============================================================================

-- | BFS with step-by-step tracing
bfsTraced :: NodeId -> Graph -> TracedResult SearchResult
bfsTraced start graph = search initialState (List.singleton start)
  where
  initialState =
    { distances: Map.singleton start 0.0
    , parents: Map.empty
    , visited: []
    , steps: []
    }

  search state List.Nil = toResult state
  search state queue =
    case List.uncons queue of
      Nothing -> toResult state
      Just { head: current, tail: rest } ->
        if Array.elem current state.visited
        then search state rest
        else
          let visited' = Array.snoc state.visited current
              steps' = Array.snoc state.steps (Visit current)
              currentDepth = fromMaybe 0.0 $ Map.lookup current state.distances
              neighborNodes = neighbors current graph
              unvisited = Array.filter (\n -> not (Map.member n.neighbor state.distances)) neighborNodes
              newQueue = rest <> List.fromFoldable (map _.neighbor unvisited)
              newDistances = foldl (\m n -> Map.insert n.neighbor (currentDepth + 1.0) m)
                               state.distances unvisited
              newParents = foldl (\m n -> Map.insert n.neighbor current m)
                             state.parents unvisited
              exploreSteps = map (\n -> Explore current n.neighbor (currentDepth + 1.0)) unvisited
          in search
               { distances: newDistances
               , parents: newParents
               , visited: visited'
               , steps: steps' <> exploreSteps
               }
               newQueue

  toResult state =
    { result:
        { distances: state.distances
        , parents: state.parents
        , visited: state.visited
        }
    , steps: state.steps
    , explored: Set.fromFoldable state.visited
    }

-- =============================================================================
-- Traced DFS
-- =============================================================================

-- | DFS with step-by-step tracing
dfsTraced :: NodeId -> Graph -> TracedResult SearchResult
dfsTraced start graph =
  let result = search
        { distances: Map.empty
        , parents: Map.empty
        , visited: []
        , steps: []
        , time: 0.0
        } start
  in { result:
         { distances: result.distances
         , parents: result.parents
         , visited: result.visited
         }
     , steps: result.steps
     , explored: Set.fromFoldable result.visited
     }
  where
  search :: TracedDFSState -> NodeId -> TracedDFSState
  search state node
    | Map.member node state.distances = state
    | otherwise =
        let time' = state.time + 1.0
            visitStep = Visit node
            state' = state
              { distances = Map.insert node time' state.distances
              , visited = Array.snoc state.visited node
              , steps = Array.snoc state.steps visitStep
              , time = time'
              }
            neighborNodes = neighbors node graph
            finalState = foldl (\s n ->
              if Map.member n.neighbor s.distances
              then s
              else
                let exploreStep = Explore node n.neighbor s.time
                    s' = s { steps = Array.snoc s.steps exploreStep
                           , parents = Map.insert n.neighbor node s.parents
                           }
                in search s' n.neighbor
            ) state' neighborNodes
            -- Add backtrack step after exploring all children
            backtrackStep = Backtrack node
        in finalState { steps = Array.snoc finalState.steps backtrackStep }

type TracedDFSState =
  { distances :: Map NodeId Number
  , parents :: Map NodeId NodeId
  , visited :: Array NodeId
  , steps :: Array SearchStep
  , time :: Number
  }

-- =============================================================================
-- Helpers
-- =============================================================================

infinity :: Number
infinity = 1.0e308

reconstructPath :: Map NodeId NodeId -> NodeId -> NodeId -> Path
reconstructPath parents start goal = go [goal] goal
  where
  go path node
    | node == start = path
    | otherwise = case Map.lookup node parents of
        Nothing -> path
        Just parent -> go (Array.cons parent path) parent

unsafeHead :: forall a. Array a -> a
unsafeHead arr = case Array.head arr of
  Just x -> x
  Nothing -> unsafeHead arr
