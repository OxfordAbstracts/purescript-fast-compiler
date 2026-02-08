-- | Graph Types
-- |
-- | Core data structures for weighted graphs.
module Data.Graph.Types
  ( NodeId(..)
  , Edge(..)
  , EdgeId(..)
  , Graph(..)
  , Path
  , mkGraph
  , nodes
  , edges
  , neighbors
  , edgeWeight
  , updateWeight
  , nodePositions
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)

-- | Node identifier
newtype NodeId = NodeId String

derive instance eqNodeId :: Eq NodeId
derive instance ordNodeId :: Ord NodeId

instance showNodeId :: Show NodeId where
  show (NodeId s) = s

-- | Edge identifier (ordered pair of nodes)
newtype EdgeId = EdgeId { from :: NodeId, to :: NodeId }

derive instance eqEdgeId :: Eq EdgeId
derive instance ordEdgeId :: Ord EdgeId

instance showEdgeId :: Show EdgeId where
  show (EdgeId e) = show e.from <> " → " <> show e.to

-- | Weighted edge
type Edge =
  { from :: NodeId
  , to :: NodeId
  , weight :: Number
  }

-- | A path is a sequence of nodes
type Path = Array NodeId

-- | Graph with nodes and weighted edges
-- | Stored as adjacency list for efficient neighbor lookup
newtype Graph = Graph
  { nodeSet :: Array NodeId
  , edgeList :: Array Edge
  , adjacency :: Map NodeId (Array { neighbor :: NodeId, weight :: Number })
  , positions :: Map NodeId { x :: Number, y :: Number }
  }

-- | Create a graph from nodes and edges
mkGraph :: Array NodeId -> Array Edge -> Graph
mkGraph nodeSet edgeList = Graph
  { nodeSet
  , edgeList
  , adjacency: buildAdjacency edgeList
  , positions: Map.empty  -- Will be set by force simulation
  }

-- | Build adjacency list from edges (bidirectional)
buildAdjacency :: Array Edge -> Map NodeId (Array { neighbor :: NodeId, weight :: Number })
buildAdjacency edgeList = Array.foldl addEdge Map.empty edgeList
  where
  addEdge acc edge =
    let fwd = { neighbor: edge.to, weight: edge.weight }
        bwd = { neighbor: edge.from, weight: edge.weight }
    in acc
      # addNeighbor edge.from fwd
      # addNeighbor edge.to bwd

  addNeighbor node neighbor m =
    Map.alter (Just <<< Array.cons neighbor <<< fromMaybe []) node m

-- | Get all nodes
nodes :: Graph -> Array NodeId
nodes (Graph g) = g.nodeSet

-- | Get all edges
edges :: Graph -> Array Edge
edges (Graph g) = g.edgeList

-- | Get neighbors of a node with their edge weights
neighbors :: NodeId -> Graph -> Array { neighbor :: NodeId, weight :: Number }
neighbors nodeId (Graph g) = fromMaybe [] $ Map.lookup nodeId g.adjacency

-- | Get weight of a specific edge
edgeWeight :: NodeId -> NodeId -> Graph -> Maybe Number
edgeWeight from to graph =
  Array.find (\n -> n.neighbor == to) (neighbors from graph)
    <#> _.weight

-- | Update the weight of an edge
updateWeight :: NodeId -> NodeId -> Number -> Graph -> Graph
updateWeight from to newWeight (Graph g) = Graph $ g
  { edgeList = map updateEdge g.edgeList
  , adjacency = buildAdjacency (map updateEdge g.edgeList)
  }
  where
  updateEdge edge
    | (edge.from == from && edge.to == to) ||
      (edge.from == to && edge.to == from) = edge { weight = newWeight }
    | otherwise = edge

-- | Get/set node positions (for visualization)
nodePositions :: Graph -> Map NodeId { x :: Number, y :: Number }
nodePositions (Graph g) = g.positions
