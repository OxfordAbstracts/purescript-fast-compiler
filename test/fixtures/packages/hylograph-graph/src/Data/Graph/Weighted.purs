-- | Data.Graph.Weighted
-- |
-- | Weighted directed graph with efficient forward and reverse adjacency lookups.
-- | This is designed for flow graphs like Sankey diagrams where we need both
-- | outgoing edges (for forward traversal) and incoming edges (for backward traversal).
module Data.Graph.Weighted
  ( WeightedDigraph
  , WeightedEdge
  , empty
  , fromEdges
  , addEdge
  , nodes
  , edges
  , outgoing
  , incoming
  , sources
  , sinks
  , nodeCount
  , edgeCount
  , hasNode
  , hasEdge
  , toSimpleGraph
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Data.Graph.Algorithms (SimpleGraph)

-- | A weighted edge in a directed graph
type WeightedEdge node weight =
  { source :: node
  , target :: node
  , weight :: weight
  }

-- | A weighted directed graph with efficient forward and reverse adjacency.
-- |
-- | Maintains both forward (source -> targets) and reverse (target -> sources)
-- | adjacency maps for O(1) lookups in both directions.
newtype WeightedDigraph node weight = WeightedDigraph
  { nodeSet :: Set node
  , edgeList :: Array (WeightedEdge node weight)
  , forward :: Map node (Array { target :: node, weight :: weight })
  , reverse :: Map node (Array { source :: node, weight :: weight })
  }

-- | Create an empty weighted digraph
empty :: forall node weight. WeightedDigraph node weight
empty = WeightedDigraph
  { nodeSet: Set.empty
  , edgeList: []
  , forward: Map.empty
  , reverse: Map.empty
  }

-- | Build a weighted digraph from an array of edges.
-- |
-- | This is the primary constructor. Nodes are inferred from edges.
-- | For isolated nodes (no edges), use `addEdge` or extend this API.
fromEdges :: forall node weight. Ord node => Array (WeightedEdge node weight) -> WeightedDigraph node weight
fromEdges edgeArray = foldl (\g e -> addEdge e.source e.target e.weight g) empty edgeArray

-- | Add an edge to the graph.
-- |
-- | If the edge already exists, it is NOT replaced (first edge wins).
-- | Both source and target nodes are added to the node set.
addEdge :: forall node weight. Ord node => node -> node -> weight -> WeightedDigraph node weight -> WeightedDigraph node weight
addEdge source target weight (WeightedDigraph g) = WeightedDigraph
  { nodeSet: Set.insert source $ Set.insert target g.nodeSet
  , edgeList: Array.snoc g.edgeList { source, target, weight }
  , forward: Map.alter (addToForward target weight) source g.forward
  , reverse: Map.alter (addToReverse source weight) target g.reverse
  }
  where
    addToForward :: node -> weight -> Maybe (Array { target :: node, weight :: weight }) -> Maybe (Array { target :: node, weight :: weight })
    addToForward t w Nothing = Just [{ target: t, weight: w }]
    addToForward t w (Just arr) = Just $ Array.snoc arr { target: t, weight: w }

    addToReverse :: node -> weight -> Maybe (Array { source :: node, weight :: weight }) -> Maybe (Array { source :: node, weight :: weight })
    addToReverse s w Nothing = Just [{ source: s, weight: w }]
    addToReverse s w (Just arr) = Just $ Array.snoc arr { source: s, weight: w }

-- | Get all nodes in the graph
nodes :: forall node weight. WeightedDigraph node weight -> Array node
nodes (WeightedDigraph g) = Set.toUnfoldable g.nodeSet

-- | Get all edges in the graph (in insertion order)
edges :: forall node weight. WeightedDigraph node weight -> Array (WeightedEdge node weight)
edges (WeightedDigraph g) = g.edgeList

-- | Get outgoing edges from a node (O(1) lookup)
-- |
-- | Returns array of { target, weight } for edges source -> target
outgoing :: forall node weight. Ord node => node -> WeightedDigraph node weight -> Array { target :: node, weight :: weight }
outgoing node (WeightedDigraph g) = fromMaybe [] $ Map.lookup node g.forward

-- | Get incoming edges to a node (O(1) lookup)
-- |
-- | Returns array of { source, weight } for edges source -> target
incoming :: forall node weight. Ord node => node -> WeightedDigraph node weight -> Array { source :: node, weight :: weight }
incoming node (WeightedDigraph g) = fromMaybe [] $ Map.lookup node g.reverse

-- | Get source nodes (nodes with no incoming edges)
-- |
-- | In a flow graph, these are entry points.
sources :: forall node weight. Ord node => WeightedDigraph node weight -> Array node
sources (WeightedDigraph g) =
  Array.filter (\n -> not $ Map.member n g.reverse) (Set.toUnfoldable g.nodeSet)

-- | Get sink nodes (nodes with no outgoing edges)
-- |
-- | In a flow graph, these are exit points.
sinks :: forall node weight. Ord node => WeightedDigraph node weight -> Array node
sinks (WeightedDigraph g) =
  Array.filter (\n -> not $ Map.member n g.forward) (Set.toUnfoldable g.nodeSet)

-- | Get the number of nodes
nodeCount :: forall node weight. WeightedDigraph node weight -> Int
nodeCount (WeightedDigraph g) = Set.size g.nodeSet

-- | Get the number of edges
edgeCount :: forall node weight. WeightedDigraph node weight -> Int
edgeCount (WeightedDigraph g) = Array.length g.edgeList

-- | Check if a node exists in the graph
hasNode :: forall node weight. Ord node => node -> WeightedDigraph node weight -> Boolean
hasNode node (WeightedDigraph g) = Set.member node g.nodeSet

-- | Check if an edge exists (ignoring weight)
hasEdge :: forall node weight. Ord node => node -> node -> WeightedDigraph node weight -> Boolean
hasEdge source target (WeightedDigraph g) =
  case Map.lookup source g.forward of
    Nothing -> false
    Just arr -> Array.any (\e -> e.target == target) arr

-- | Convert to SimpleGraph (for algorithm reuse)
-- |
-- | Drops weights and converts to adjacency-set representation.
toSimpleGraph :: forall node weight. Ord node => WeightedDigraph node weight -> SimpleGraph node
toSimpleGraph (WeightedDigraph g) =
  { nodes: Set.toUnfoldable g.nodeSet
  , edges: Map.fromFoldable $ map convertEntry $ (Map.toUnfoldable g.forward :: Array (Tuple node (Array { target :: node, weight :: weight })))
  }
  where
    convertEntry :: Tuple node (Array { target :: node, weight :: weight }) -> Tuple node (Set node)
    convertEntry (Tuple source targets) = Tuple source (Set.fromFoldable $ map _.target targets)
