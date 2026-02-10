-- | DataViz.Layout.Chord
-- |
-- | Pure PureScript chord diagram layout algorithm.
-- |
-- | A chord diagram shows relationships between nodes arranged in a circle,
-- | with ribbons (curved bands) connecting related nodes.
-- |
-- | This module provides pure layout computation that can be used with
-- | any rendering backend (Hylograph HATS, D3, Canvas, SVG, etc.)
-- |
-- | Example usage:
-- | ```purescript
-- | import DataViz.Layout.Chord (layout)
-- |
-- | let matrix = [[0,1,2],[1,0,3],[2,3,0]]
-- |     result = layout matrix
-- | -- result.groups contains arc positions
-- | -- result.chords contains ribbon connections
-- | ```
-- |
-- | For rendering, use the path generators in Hylograph.Expr.Path.Generators:
-- | - `genArc` for the arc segments
-- | - `genRibbon` for the ribbon paths
module DataViz.Layout.Chord
  ( module DataViz.Layout.Chord.Types
  , module DataViz.Layout.Chord.Layout
  ) where

import DataViz.Layout.Chord.Types
import DataViz.Layout.Chord.Layout
