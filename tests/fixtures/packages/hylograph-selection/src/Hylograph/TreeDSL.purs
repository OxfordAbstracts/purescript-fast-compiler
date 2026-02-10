-- | PSD3.TreeDSL - Finally Tagless Tree Building
-- |
-- | This module provides the extensible, typeclass-based API for building
-- | visualization trees. Unlike the concrete `Tree` ADT, this approach allows
-- | extensions without modifying the core library.
-- |
-- | ## Design
-- |
-- | `TreeDSL` is a typeclass parameterized by a type constructor `tree`:
-- |
-- | ```purescript
-- | class TreeDSL tree where
-- |   named :: ElementType -> String -> Array (Attribute d) -> tree d
-- |   ...
-- | ```
-- |
-- | Different implementations can provide different behaviors:
-- | - `Tree` (from PSD3.AST) - builds a concrete AST for later interpretation
-- | - Direct DOM interpreter - renders immediately
-- | - Mermaid interpreter - generates diagram code
-- |
-- | ## Extension
-- |
-- | New features are added via subclasses:
-- |
-- | ```purescript
-- | class TreeDSL tree <= ShapeTreeDSL tree where
-- |   fromSpec :: (d -> ShapeSpec d) -> tree d
-- | ```
-- |
-- | Extensions don't require modifying the core `TreeDSL` class.
-- |
module Hylograph.TreeDSL
  ( class TreeDSL
  , named
  , elem
  , withChild
  , withChildren
  , withBehaviors
  , joinData
  , nestedJoin
  , updateJoin
  , updateNestedJoin
  , conditionalRender
  , conditionalRenderOr
  , localCoordSpace
  , localCoordSpaceFixed
  -- * Types
  , PhaseBehavior
  , GUPBehaviors
  -- * Operators
  , (>:)
  , (+:)
  -- * Helpers
  , beside
  , siblings
  ) where

import Prelude

import Data.Maybe (Maybe)
import Hylograph.Internal.Attribute (Attribute)
import Hylograph.Internal.Behavior.Types (Behavior)
import Hylograph.Internal.Selection.Types (ElementType)
import Hylograph.Internal.Transition.Types (TransitionConfig)

-- | GUP phase behavior specification (re-exported from AST for convenience)
type PhaseBehavior datum =
  { attrs :: Array (Attribute datum)
  , transition :: Maybe TransitionConfig
  }

-- | Complete GUP behavior specification
type GUPBehaviors datum =
  { enter :: Maybe (PhaseBehavior datum)
  , update :: Maybe (PhaseBehavior datum)
  , exit :: Maybe (PhaseBehavior datum)
  }

-- =============================================================================
-- The Core TreeDSL Typeclass
-- =============================================================================

-- | The core tree-building DSL.
-- |
-- | `tree` is a type constructor: `tree :: Type -> Type`
-- | where the parameter is the datum type.
-- |
-- | Implementations include:
-- | - `Tree` from PSD3.AST (builds a data structure)
-- | - Direct interpreters (could render immediately)
-- | - Analysis interpreters (could extract metadata)
class TreeDSL (tree :: Type -> Type) where

  -- | Create a named element.
  -- |
  -- | Named elements can be retrieved after rendering.
  -- | This is the workhorse for building visualization structure.
  -- |
  -- | Example:
  -- | ```purescript
  -- | named SVG "svg" [width 800.0, height 600.0]
  -- | ```
  named
    :: forall datum
     . ElementType
    -> String
    -> Array (Attribute datum)
    -> tree datum

  -- | Create an anonymous element.
  -- |
  -- | Anonymous elements won't appear in the returned selections.
  -- | Use for structural elements that don't need later access.
  -- |
  -- | Example:
  -- | ```purescript
  -- | elem Group [class_ "container"]
  -- | ```
  elem
    :: forall datum
     . ElementType
    -> Array (Attribute datum)
    -> tree datum

  -- | Add a single child to a tree.
  -- |
  -- | Example:
  -- | ```purescript
  -- | parent `withChild` child
  -- | ```
  withChild
    :: forall datum
     . tree datum
    -> tree datum
    -> tree datum

  -- | Add multiple children to a tree.
  -- |
  -- | Example:
  -- | ```purescript
  -- | parent `withChildren` [child1, child2, child3]
  -- | ```
  withChildren
    :: forall datum
     . tree datum
    -> Array (tree datum)
    -> tree datum

  -- | Attach behaviors (zoom, drag, click handlers) to a tree.
  -- |
  -- | Example:
  -- | ```purescript
  -- | svg `withBehaviors` [Zoom config, Drag SimpleDrag]
  -- | ```
  withBehaviors
    :: forall datum
     . tree datum
    -> Array (Behavior datum)
    -> tree datum

  -- | Create a data join.
  -- |
  -- | The template function builds a subtree for each datum.
  -- | The join becomes a named selection representing the collection.
  -- |
  -- | Example:
  -- | ```purescript
  -- | joinData "circles" "circle" dataPoints $ \d ->
  -- |   elem Circle [cx d.x, cy d.y, radius 5.0]
  -- | ```
  joinData
    :: forall datum
     . String                      -- Name for this join
    -> String                      -- Element key (e.g., "circle", "g")
    -> Array datum                 -- Data to join
    -> (datum -> tree datum)       -- Template builder
    -> tree datum

  -- | Create a nested data join with type decomposition.
  -- |
  -- | Allows the datum type to change during decomposition.
  -- | Essential for nested structures like tables.
  -- |
  -- | Example:
  -- | ```purescript
  -- | nestedJoin "rows" "tr" tableData (_.cells) $ \cell ->
  -- |   elem Td [textContent cell.value]
  -- | ```
  nestedJoin
    :: forall outerDatum innerDatum
     . String
    -> String
    -> Array outerDatum
    -> (outerDatum -> Array innerDatum)
    -> (innerDatum -> tree innerDatum)
    -> tree outerDatum

  -- | Create an update join with GUP (enter/update/exit) behaviors.
  -- |
  -- | Declaratively specifies animations and transitions for each phase.
  -- |
  -- | Example:
  -- | ```purescript
  -- | updateJoin "nodes" "g" nodes template
  -- |   { enter: Just { attrs: [opacity 0.0], transition: Just fadeIn }
  -- |   , update: Just { attrs: [], transition: Just move }
  -- |   , exit: Just { attrs: [opacity 0.0], transition: Just fadeOut }
  -- |   , keyFn: Just _.id
  -- |   }
  -- | ```
  updateJoin
    :: forall datum
     . String
    -> String
    -> Array datum
    -> (datum -> tree datum)
    -> { enter :: Maybe (PhaseBehavior datum)
       , update :: Maybe (PhaseBehavior datum)
       , exit :: Maybe (PhaseBehavior datum)
       , keyFn :: Maybe (datum -> String)
       }
    -> tree datum

  -- | Create an update nested join with type decomposition and GUP.
  -- |
  -- | Combines `nestedJoin` and `updateJoin` - the recommended pattern
  -- | for most dynamic visualizations.
  updateNestedJoin
    :: forall outerDatum innerDatum
     . String
    -> String
    -> Array outerDatum
    -> (outerDatum -> Array innerDatum)
    -> (innerDatum -> tree innerDatum)
    -> GUPBehaviors innerDatum
    -> tree outerDatum

  -- | Conditional rendering based on predicates.
  -- |
  -- | Enables chimeric visualizations - different visual representations
  -- | for different data shapes.
  -- |
  -- | Example:
  -- | ```purescript
  -- | conditionalRender
  -- |   [ { predicate: isCluster, spec: clusterViz }
  -- |   , { predicate: isLeaf, spec: leafViz }
  -- |   ]
  -- | ```
  conditionalRender
    :: forall datum
     . Array { predicate :: datum -> Boolean, spec :: datum -> tree datum }
    -> tree datum

  -- | Create a local coordinate space for embedded visualizations.
  -- |
  -- | The child tree renders in its own coordinate system.
  localCoordSpace
    :: forall datum
     . { scaleX :: datum -> Number, scaleY :: datum -> Number }
    -> tree datum
    -> tree datum

-- =============================================================================
-- Derived Combinators (work for any TreeDSL instance)
-- =============================================================================

-- | Conditional render with a fallback for unmatched cases.
conditionalRenderOr
  :: forall tree datum
   . TreeDSL tree
  => Array { predicate :: datum -> Boolean, spec :: datum -> tree datum }
  -> (datum -> tree datum)
  -> tree datum
conditionalRenderOr cases fallback =
  conditionalRender (cases <> [{ predicate: \_ -> true, spec: fallback }])

-- | Local coordinate space with fixed dimensions.
localCoordSpaceFixed
  :: forall tree datum
   . TreeDSL tree
  => Number
  -> Number
  -> tree datum
  -> tree datum
localCoordSpaceFixed w h = localCoordSpace { scaleX: \_ -> w, scaleY: \_ -> h }

-- | Combine two trees as siblings (for use with `withChildren`).
beside :: forall tree datum. tree datum -> tree datum -> Array (tree datum)
beside left right = [left, right]

-- | Identity function for grouping siblings.
siblings :: forall tree datum. Array (tree datum) -> Array (tree datum)
siblings = identity

-- =============================================================================
-- Operators
-- =============================================================================

infixl 6 withChild as >:
infixl 5 beside as +:
