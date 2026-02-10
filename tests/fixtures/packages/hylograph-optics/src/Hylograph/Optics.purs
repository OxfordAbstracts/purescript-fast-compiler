-- | Hylograph Optics
-- |
-- | A comprehensive optics library for Hylograph data structures.
-- |
-- | This module provides lenses, prisms, traversals, and affine traversals
-- | for working with Trees, Graphs, and other visualization data structures.
-- |
-- | ## Quick Reference
-- |
-- | **Trees:**
-- | - `_root` - Focus on root value
-- | - `_children` - Focus on child list
-- | - `_leaves` - Traverse all leaves
-- | - `_atDepth n` - Traverse nodes at depth n
-- | - `_nodeAtPath [i,j,k]` - Focus on node at path
-- |
-- | **Graphs:**
-- | - `_node id` - Focus on specific node
-- | - `_edge from to` - Focus on specific edge
-- | - `_edgeWeight from to` - Focus on edge weight
-- | - `_neighbors id` - Traverse neighbors
-- | - `_nodesWhere pred` - Traverse matching nodes
-- |
-- | ## Example Usage
-- |
-- | ```purescript
-- | import Hylograph.Optics
-- | import Data.Lens (view, set, over, preview, toListOf)
-- |
-- | -- Trees
-- | view _root myTree                    -- Get root value
-- | set _root 100 myTree                 -- Set root to 100
-- | over _leaves (*2) myTree             -- Double all leaves
-- | toListOf (_atDepth 2) myTree         -- Get all grandchildren
-- |
-- | -- Graphs
-- | preview (_node (NodeId "A")) graph   -- Get node if exists
-- | set (_edgeWeight a b) 2.5 graph      -- Update edge weight
-- | toListOf (_neighbors a) graph        -- Get all neighbors of A
-- | ```
module Hylograph.Optics
  ( module Hylograph.Optics.Tree
  , module Hylograph.Optics.Graph
  ) where

import Hylograph.Optics.Tree
import Hylograph.Optics.Graph
