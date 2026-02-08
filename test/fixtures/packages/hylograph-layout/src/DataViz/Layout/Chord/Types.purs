-- | DataViz.Layout.Chord.Types
-- |
-- | Types for chord diagram visualization.
-- |
-- | A chord diagram shows relationships between nodes arranged in a circle,
-- | with ribbons (curved bands) connecting related nodes.
-- |
-- | The layout takes a square matrix where:
-- | - matrix[i][j] represents the flow/connection strength from node i to node j
-- | - Each node gets an arc proportional to its total connections
-- | - Ribbons connect arcs, with width proportional to connection strength
module DataViz.Layout.Chord.Types
  ( ChordMatrix(..)
  , ChordGroup(..)
  , Chord(..)
  , ChordLayout(..)
  , LayoutConfig
  , defaultConfig
  ) where

import Prelude

import Data.Number (pi)

-- | Input matrix for chord diagram
-- | Contains connection weights and node names
type ChordMatrix =
  { matrix :: Array (Array Number)  -- NxN matrix of connection weights
  , names :: Array String           -- Node names (length N)
  }

-- | A group (arc) in the chord layout
-- | Represents a single node's portion of the circle perimeter
type ChordGroup =
  { index :: Int           -- Node index in the matrix
  , startAngle :: Number   -- Start angle in radians
  , endAngle :: Number     -- End angle in radians
  , value :: Number        -- Total value (row sum)
  }

-- | A chord (ribbon) connecting two groups
-- | Represents the flow between two nodes
type Chord =
  { source :: ChordGroup   -- Source arc segment for this chord
  , target :: ChordGroup   -- Target arc segment for this chord
  }

-- | Complete chord layout ready for rendering
type ChordLayout =
  { groups :: Array ChordGroup   -- Arc groups around the perimeter
  , chords :: Array Chord        -- Ribbons connecting groups
  }

-- | Configuration for chord layout
type LayoutConfig =
  { padAngle :: Number      -- Padding between arcs in radians (default: 0.0)
  , startAngle :: Number    -- Starting angle (default: 0.0)
  , endAngle :: Number      -- Ending angle (default: 2π)
  , sortGroups :: Boolean   -- Whether to sort groups by value (default: false)
  , sortChords :: Boolean   -- Whether to sort chords by value (default: false)
  }

-- | Default layout configuration
defaultConfig :: LayoutConfig
defaultConfig =
  { padAngle: 0.0
  , startAngle: 0.0
  , endAngle: 2.0 * pi
  , sortGroups: false
  , sortChords: false
  }
