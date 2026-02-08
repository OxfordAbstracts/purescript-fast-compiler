-- | PSD3.Unified.Join - Composable Join Combinators
-- |
-- | This module decomposes PSD3's four Join constructors into orthogonal,
-- | composable pieces. Instead of a Cartesian product of features:
-- |
-- | ```
-- | Join              = basic
-- | NestedJoin        = basic + decompose
-- | UpdateJoin        = basic + GUP
-- | UpdateNestedJoin  = basic + decompose + GUP
-- | ```
-- |
-- | We have independent combinators that compose:
-- |
-- | ```
-- | join data template                           -- basic
-- | withDecompose decomp (join data template)    -- + decomposition
-- | withGUP behaviors (join data template)       -- + GUP
-- | withGUP behaviors (withDecompose decomp ...) -- + both
-- | ```
-- |
-- | ## Benefits
-- |
-- | 1. **Extensibility**: Add new features without exponential constructors
-- | 2. **Composability**: Mix and match features freely
-- | 3. **Clarity**: Each combinator does one thing
-- | 4. **Unification**: Same patterns work in viz and spreadsheet contexts
-- |
-- | ## Migration
-- |
-- | Old code using Join constructors continues to work unchanged.
-- | New code can use the composable combinators.
-- |
-- | See `PSD3.Unified.Join.Compat` for automatic migration shims.
module Hylograph.Unified.Join
  ( -- * Core Join Specification
    JoinSpec(..)
  , JoinConfig
    -- * Smart Constructors
  , join
    -- * Decomposition Combinator
  , withDecompose
  , Decomposer
    -- * GUP Combinator
  , withGUP
  , GUPSpec
  , PhaseSpec
  , enterSpec
  , updateSpec
  , exitSpec
  , noTransition
    -- * Full Specification Builder
  , JoinBuilder
  , buildJoin
  , basicJoin
  , nestedJoin
  , gupJoin
  , fullJoin
    -- * Execute Join (Build Tree)
  , toTree
    -- * Convenience Re-exports
  , module Exports
  ) where

import Prelude hiding (join)

import Data.Maybe (Maybe(..))
import Hylograph.Internal.Attribute (Attribute)
import Hylograph.Internal.Transition.Types (TransitionConfig) as Exports
import Hylograph.Internal.Transition.Types (TransitionConfig)
import Hylograph.AST (Tree)
import Hylograph.AST as AST
import Unsafe.Coerce (unsafeCoerce)

-- =============================================================================
-- Core Join Types
-- =============================================================================

-- | Configuration for a single GUP phase (enter, update, or exit)
-- |
-- | - `attrs`: Attributes to apply for this phase
-- | - `transition`: Optional animation configuration
type PhaseSpec datum =
  { attrs :: Array (Attribute datum)
  , transition :: Maybe TransitionConfig
  }

-- | Complete GUP specification with all three phases
-- |
-- | Each phase is optional - if Nothing, default behavior is used.
type GUPSpec datum =
  { enter :: Maybe (PhaseSpec datum)
  , update :: Maybe (PhaseSpec datum)
  , exit :: Maybe (PhaseSpec datum)
  }

-- | A decomposer extracts inner data from outer data
-- |
-- | Example: `_.points :: SceneData -> Array DataPoint`
type Decomposer outer inner = outer -> Array inner

-- | Full join configuration
-- |
-- | This captures ALL the information needed to perform any kind of join,
-- | with optional decomposition and GUP behaviors.
type JoinConfig outer inner =
  { name :: String
  , key :: String
  , keyFn :: Maybe (inner -> String)
  , decompose :: Maybe (Decomposer outer inner)
  , gup :: Maybe (GUPSpec inner)
  }

-- | A join specification: data + template + config
-- |
-- | The outer/inner type parameters allow type-changing joins.
-- | For simple joins where outer = inner, they'll be the same.
data JoinSpec outer inner
  = JoinSpec
      { data_ :: Array outer
      , template :: inner -> Tree inner
      , config :: JoinConfig outer inner
      }

-- =============================================================================
-- Smart Constructors
-- =============================================================================

-- | Create a basic join specification with key function
-- |
-- | This is the foundation - data, a name, keyFn for identity, and a template.
-- | Decomposition and GUP can be added with combinators.
-- |
-- | The key function extracts identity for matching in updates. This is
-- | mandatory because dynamic updates need stable identity matching.
-- |
-- | ```purescript
-- | join "nodes" "g" nodeData _.id $ \node ->
-- |   elem Group [...]
-- | ```
join :: forall datum.
  String ->                      -- Name
  String ->                      -- Element key
  Array datum ->                 -- Data
  (datum -> String) ->           -- Key function for identity (mandatory)
  (datum -> Tree datum) ->       -- Template
  JoinSpec datum datum
join name key data_ keyFn template =
  JoinSpec
    { data_
    , template
    , config:
        { name
        , key
        , keyFn: Just keyFn
        , decompose: Nothing
        , gup: Nothing
        }
    }

-- =============================================================================
-- Decomposition Combinator
-- =============================================================================

-- | Add decomposition to a join
-- |
-- | Decomposition extracts inner data from outer data, enabling type changes.
-- | This replaces `NestedJoin`.
-- |
-- | ```purescript
-- | join "rows" "tr" tableData identity
-- |   # withDecompose (_.cells)  -- Extract cells from each row
-- | ```
-- |
-- | Or with type change:
-- | ```purescript
-- | join "circles" "circle" [sceneData] identity
-- |   # withDecompose (_.points)  -- SceneData -> Array DataPoint
-- | ```
withDecompose :: forall outer inner.
  (outer -> Array inner) ->       -- Decomposer function
  JoinSpec outer outer ->         -- Input join (typed for outer)
  JoinSpec outer inner            -- Output join (typed for inner)
withDecompose decomposer (JoinSpec spec) =
  JoinSpec
    { data_: spec.data_
    , template: unsafeCoerceTemplate spec.template  -- Template now typed for inner
    , config:
        { name: spec.config.name
        , key: spec.config.key
        , keyFn: unsafeCoerce spec.config.keyFn  -- keyFn type changes with inner type
        , decompose: Just decomposer
        , gup: Nothing  -- GUP must be re-added after decompose (types change)
        }
    }
  where
  -- These coercions are safe because:
  -- 1. The decomposer transforms outer -> Array inner
  -- 2. The template will receive inner values after decomposition
  -- 3. The types align at the call site where both functions are provided
  unsafeCoerceTemplate :: (outer -> Tree outer) -> (inner -> Tree inner)
  unsafeCoerceTemplate = unsafeCoerce

-- =============================================================================
-- GUP Combinator
-- =============================================================================

-- | Add GUP (General Update Pattern) behaviors to a join
-- |
-- | GUP specifies enter/update/exit behaviors with optional transitions.
-- | This replaces `UpdateJoin`.
-- |
-- | ```purescript
-- | join "circles" "circle" circleData $ \d -> ...
-- |   # withGUP
-- |       { enter: Just { attrs: [opacity 0.0], transition: Just fadeIn }
-- |       , update: Just { attrs: [], transition: Just move }
-- |       , exit: Just { attrs: [opacity 0.0], transition: Just fadeOut }
-- |       }
-- | ```
withGUP :: forall outer inner.
  GUPSpec inner ->                -- GUP behaviors
  JoinSpec outer inner ->         -- Input join
  JoinSpec outer inner            -- Output join with GUP
withGUP gupSpec (JoinSpec spec) =
  JoinSpec
    { data_: spec.data_
    , template: spec.template
    , config: spec.config { gup = Just gupSpec }
    }

-- =============================================================================
-- Phase Spec Builders
-- =============================================================================

-- | Create an enter phase specification
enterSpec :: forall datum.
  Array (Attribute datum) ->   -- Initial attributes
  Maybe TransitionConfig ->    -- Optional transition
  PhaseSpec datum
enterSpec attrs transition = { attrs, transition }

-- | Create an update phase specification
updateSpec :: forall datum.
  Array (Attribute datum) ->   -- Update attributes
  Maybe TransitionConfig ->    -- Optional transition
  PhaseSpec datum
updateSpec attrs transition = { attrs, transition }

-- | Create an exit phase specification
exitSpec :: forall datum.
  Array (Attribute datum) ->   -- Exit attributes
  Maybe TransitionConfig ->    -- Optional transition
  PhaseSpec datum
exitSpec attrs transition = { attrs, transition }

-- | Phase with no transition (immediate attribute application)
noTransition :: forall datum. Array (Attribute datum) -> PhaseSpec datum
noTransition attrs = { attrs, transition: Nothing }

-- =============================================================================
-- Join Builder (Alternative API)
-- =============================================================================

-- | Builder type for constructing joins step by step
type JoinBuilder outer inner =
  { name :: String
  , key :: String
  , data_ :: Array outer
  , keyFn :: Maybe (inner -> String)
  , decompose :: Maybe (outer -> Array inner)
  , gup :: Maybe (GUPSpec inner)
  }

-- | Build a join from a builder spec
-- |
-- | This is the low-level API for full control.
buildJoin :: forall outer inner.
  JoinBuilder outer inner ->
  (inner -> Tree inner) ->
  JoinSpec outer inner
buildJoin builder template =
  JoinSpec
    { data_: builder.data_
    , template
    , config:
        { name: builder.name
        , key: builder.key
        , keyFn: builder.keyFn
        , decompose: unsafeCoerce builder.decompose
        , gup: builder.gup
        }
    }

-- =============================================================================
-- Convenience Constructors (mirrors old API)
-- =============================================================================

-- | Basic join (equivalent to old `Join` constructor)
basicJoin :: forall datum.
  String ->                    -- Name
  String ->                    -- Key
  Array datum ->               -- Data
  (datum -> String) ->         -- Key function for identity
  (datum -> Tree datum) ->     -- Template
  JoinSpec datum datum
basicJoin = join

-- | Nested join with decomposition (equivalent to old `NestedJoin`)
nestedJoin :: forall outer inner.
  String ->                        -- Name
  String ->                        -- Key
  Array outer ->                   -- Outer data
  (outer -> Array inner) ->        -- Decomposer
  (inner -> String) ->             -- Key function for inner identity
  (inner -> Tree inner) ->         -- Template
  JoinSpec outer inner
nestedJoin name key data_ decomposer keyFn template =
  join name key data_ (unsafeCoerce keyFn) (unsafeCoerce template)
    # withDecompose decomposer

-- | GUP join (equivalent to old `UpdateJoin`)
gupJoin :: forall datum.
  String ->                        -- Name
  String ->                        -- Key
  Array datum ->                   -- Data
  (datum -> String) ->             -- Key function for identity
  (datum -> Tree datum) ->         -- Template
  GUPSpec datum ->                 -- GUP behaviors
  JoinSpec datum datum
gupJoin name key data_ keyFn template gup =
  join name key data_ keyFn template
    # withGUP gup

-- | Full join with decomposition and GUP (equivalent to old `UpdateNestedJoin`)
fullJoin :: forall outer inner.
  String ->                        -- Name
  String ->                        -- Key
  Array outer ->                   -- Outer data
  (outer -> Array inner) ->        -- Decomposer
  (inner -> String) ->             -- Key function for inner identity
  (inner -> Tree inner) ->         -- Template
  GUPSpec inner ->                 -- GUP behaviors
  JoinSpec outer inner
fullJoin name key data_ decomposer keyFn template gup =
  join name key data_ (unsafeCoerce keyFn) (unsafeCoerce template)
    # withDecompose decomposer
    # withGUP gup

-- =============================================================================
-- Execute Join: Convert JoinSpec to Tree
-- =============================================================================

-- | Convert a JoinSpec to a Tree (execute the join specification)
-- |
-- | This is the final step - it produces the AST node that interpreters
-- | (D3, Mermaid, etc.) can process.
-- |
-- | ```purescript
-- | myTree :: Tree DataPoint
-- | myTree = join "circles" "circle" dataPoints circleTemplate
-- |   # withGUP myGUP
-- |   # toTree
-- | ```
-- |
-- | SAFETY: The unsafeCoerce calls in toTree are safe because:
-- |
-- | 1. **Type erasure for existentials**: PureScript lacks existential types, so we erase
-- |    the inner datum type when storing decompose/template/gup functions. The functions
-- |    were provided together at the call site (join/withDecompose/withGUP), guaranteeing
-- |    they agree on the inner type.
-- |
-- | 2. **outer = inner when no decompose**: Without a decompose function, the join operates
-- |    on outer directly (JoinSpec outer outer). The coercions are identity in this case.
-- |
-- | 3. **AST stores erased types**: The AST nodes (NestedJoin, UpdateNestedJoin) also use
-- |    type erasure internally - they recover types via the stored functions at runtime.
toTree :: forall outer inner. JoinSpec outer inner -> Tree outer
toTree (JoinSpec spec) =
  case spec.config.decompose, spec.config.gup of
    -- Basic join (no decompose, no GUP)
    -- SAFETY: When no decompose, outer = inner (join always creates JoinSpec datum datum)
    Nothing, Nothing ->
      AST.joinData spec.config.name spec.config.key
        (unsafeCoerce spec.data_)
        (unsafeCoerce spec.template)

    -- Nested join (decompose, no GUP)
    -- SAFETY: decompose and template were provided together via withDecompose
    Just decompose, Nothing ->
      AST.nestedJoin spec.config.name spec.config.key
        spec.data_
        decompose
        (unsafeCoerce spec.template)

    -- Update join (no decompose, with GUP)
    -- SAFETY: When no decompose, outer = inner, so coercions are identity
    Nothing, Just gup ->
      unsafeCoerce $
        AST.updateJoin spec.config.name spec.config.key
          (unsafeCoerce spec.data_)
          (unsafeCoerce spec.template)
          { enter: unsafeCoerce $ toMaybePhaseBehavior gup.enter
          , update: unsafeCoerce $ toMaybePhaseBehavior gup.update
          , exit: unsafeCoerce $ toMaybePhaseBehavior gup.exit
          , keyFn: unsafeCoerce spec.config.keyFn
          }

    -- Full join (decompose + GUP)
    -- SAFETY: All functions agree on inner type (provided together)
    Just decompose, Just gup ->
      AST.updateNestedJoin spec.config.name spec.config.key
        spec.data_
        decompose
        (unsafeCoerce spec.template)
        (unsafeCoerce { enter: toMaybePhaseBehavior gup.enter
        , update: toMaybePhaseBehavior gup.update
        , exit: toMaybePhaseBehavior gup.exit
        })

-- | Convert our PhaseSpec to AST's PhaseBehavior
toMaybePhaseBehavior :: forall datum. Maybe (PhaseSpec datum) -> Maybe (AST.PhaseBehavior datum)
toMaybePhaseBehavior Nothing = Nothing
toMaybePhaseBehavior (Just ps) = Just { attrs: ps.attrs, transition: ps.transition }

-- =============================================================================
-- Future: Additional Combinators
-- =============================================================================

{-
  The composable approach makes it easy to add new features:

  -- Add sorting
  withSort :: (inner -> inner -> Ordering) -> JoinSpec outer inner -> JoinSpec outer inner

  -- Add filtering
  withFilter :: (inner -> Boolean) -> JoinSpec outer inner -> JoinSpec outer inner

  -- Add grouping
  withGroupBy :: (inner -> key) -> JoinSpec outer inner -> JoinSpec outer (Tuple key (Array inner))

  -- Add pagination
  withPagination :: { offset :: Int, limit :: Int } -> JoinSpec outer inner -> JoinSpec outer inner

  These compose naturally:

  join "items" "li" items template
    # withFilter (\i -> i.active)
    # withSort (\a b -> compare a.date b.date)
    # withGUP fadeInOut
-}
