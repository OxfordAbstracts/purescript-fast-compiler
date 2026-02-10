-- | Graph Optics
-- |
-- | Lenses, traversals, and accessors for weighted graphs.
module Hylograph.Optics.Graph
  ( -- * Node Optics
    _nodes
  , getNode
  , getNodePosition
  , setNodePosition
    -- * Edge Optics
  , _edges
  , getEdge
  , getEdgeWeight
  , setEdgeWeight
    -- * Structural Traversals
  , _neighbors
  , _outEdges
  , _inEdges
    -- * Subgraph Selection
  , _nodesWhere
  , _edgesWhere
  ) where

import Prelude

import Data.Array as Array
import Data.Graph.Types (Graph(..), NodeId(..), Edge)
import Data.Lens (Lens', Traversal', lens, traversed, filtered)
import Data.Map as Map
import Data.Maybe (Maybe(..))

-- =============================================================================
-- Node Optics
-- =============================================================================

-- | Lens to all node IDs in the graph.
-- |
-- | ```purescript
-- | view _nodes graph
-- | -- => Array of all NodeIds
-- | ```
_nodes :: Lens' Graph (Array NodeId)
_nodes = lens getter setter
  where
  getter (Graph g) = g.nodeSet
  setter (Graph g) newNodes = Graph $ g { nodeSet = newNodes }

-- | Get a node by ID if it exists.
-- |
-- | ```purescript
-- | getNode (NodeId "A") graph
-- | -- => Just (NodeId "A") if exists, Nothing otherwise
-- | ```
getNode :: NodeId -> Graph -> Maybe NodeId
getNode nodeId (Graph g) =
  if Array.elem nodeId g.nodeSet
  then Just nodeId
  else Nothing

-- | Get a node's position if set.
-- |
-- | ```purescript
-- | getNodePosition (NodeId "A") graph
-- | -- => Just { x: 100.0, y: 200.0 } if positioned
-- | ```
getNodePosition :: NodeId -> Graph -> Maybe { x :: Number, y :: Number }
getNodePosition nodeId (Graph g) = Map.lookup nodeId g.positions

-- | Set a node's position.
-- |
-- | ```purescript
-- | setNodePosition (NodeId "A") { x: 100.0, y: 200.0 } graph
-- | ```
setNodePosition :: NodeId -> { x :: Number, y :: Number } -> Graph -> Graph
setNodePosition nodeId pos (Graph g) = Graph $ g
  { positions = Map.insert nodeId pos g.positions }

-- =============================================================================
-- Edge Optics
-- =============================================================================

-- | Lens to all edges in the graph.
-- |
-- | ```purescript
-- | view _edges graph
-- | -- => Array of all edges
-- | ```
_edges :: Lens' Graph (Array Edge)
_edges = lens getter setter
  where
  getter (Graph g) = g.edgeList
  setter (Graph g) newEdges = Graph $ g { edgeList = newEdges }

-- | Get an edge by source and target.
-- |
-- | ```purescript
-- | getEdge (NodeId "A") (NodeId "B") graph
-- | -- => Just edge if it exists
-- | ```
getEdge :: NodeId -> NodeId -> Graph -> Maybe Edge
getEdge from to (Graph g) =
  Array.find (\e -> e.from == from && e.to == to) g.edgeList

-- | Get an edge's weight.
-- |
-- | ```purescript
-- | getEdgeWeight (NodeId "A") (NodeId "B") graph
-- | -- => Just 1.5 (the weight)
-- | ```
getEdgeWeight :: NodeId -> NodeId -> Graph -> Maybe Number
getEdgeWeight from to graph = _.weight <$> getEdge from to graph

-- | Set an edge's weight.
-- |
-- | ```purescript
-- | setEdgeWeight (NodeId "A") (NodeId "B") 2.0 graph
-- | -- Update edge weight
-- | ```
setEdgeWeight :: NodeId -> NodeId -> Number -> Graph -> Graph
setEdgeWeight from to newWeight (Graph g) = Graph $ g
  { edgeList = map (\e ->
      if e.from == from && e.to == to
      then e { weight = newWeight }
      else e
    ) g.edgeList
  }

-- =============================================================================
-- Structural Traversals
-- =============================================================================

-- | Traverse all neighbors of a node.
-- |
-- | ```purescript
-- | toListOf (_neighbors (NodeId "A")) graph
-- | -- => All nodes connected to A
-- | ```
_neighbors :: NodeId -> Traversal' Graph NodeId
_neighbors nodeId = _edges <<< traversed <<< neighborFilter <<< neighborLens
  where
  neighborFilter = filtered (\e -> e.from == nodeId || e.to == nodeId)
  neighborLens = lens
    (\e -> if e.from == nodeId then e.to else e.from)
    (\e n -> if e.from == nodeId then e { to = n } else e { from = n })

-- | Traverse all outgoing edges from a node.
-- |
-- | ```purescript
-- | toListOf (_outEdges (NodeId "A")) graph
-- | -- => All edges where A is the source
-- | ```
_outEdges :: NodeId -> Traversal' Graph Edge
_outEdges nodeId = _edges <<< traversed <<< filtered (\e -> e.from == nodeId)

-- | Traverse all incoming edges to a node.
-- |
-- | ```purescript
-- | toListOf (_inEdges (NodeId "A")) graph
-- | -- => All edges where A is the target
-- | ```
_inEdges :: NodeId -> Traversal' Graph Edge
_inEdges nodeId = _edges <<< traversed <<< filtered (\e -> e.to == nodeId)

-- =============================================================================
-- Subgraph Selection
-- =============================================================================

-- | Traverse nodes matching a predicate.
-- |
-- | ```purescript
-- | toListOf (_nodesWhere (\(NodeId s) -> String.length s == 1)) graph
-- | -- => All single-letter node IDs
-- | ```
_nodesWhere :: (NodeId -> Boolean) -> Traversal' Graph NodeId
_nodesWhere pred = _nodes <<< traversed <<< filtered pred

-- | Traverse edges matching a predicate.
-- |
-- | ```purescript
-- | toListOf (_edgesWhere (\e -> e.weight > 1.0)) graph
-- | -- => All edges with weight > 1.0
-- | ```
_edgesWhere :: (Edge -> Boolean) -> Traversal' Graph Edge
_edgesWhere pred = _edges <<< traversed <<< filtered pred
