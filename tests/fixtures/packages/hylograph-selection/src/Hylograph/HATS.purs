-- | HATS: Hylomorphic Abstract Tree Syntax
-- |
-- | A principled AST for data visualization based on recursion schemes.
-- |
-- | The core insight: a visualization is a **transduction** from data to DOM,
-- | composed of two orthogonal choices:
-- |
-- | - **Enumeration**: How to traverse/extract elements from input (coalgebra)
-- | - **Assembly**: How to structure the output DOM (algebra)
-- |
-- | This version uses existentially-scoped data binding:
-- | - `Tree` has no type parameter - all trees compose freely with `<>`
-- | - Each `Fold` brings its own datum type `a` into scope
-- | - Attributes and behaviors inside templates capture datum via closures
module Hylograph.HATS
  ( Tree(..)
  , Enumeration(..)
  , Assembly(..)
  , TraversalOrder(..)
  , GUPSpec(..)
  , PhaseSpec(..)
  , SomeFold
  , FoldSpec
  , mkSomeFold
  , runSomeFold
  , Attr(..)
  , ThunkedBehavior(..)
  -- Smart constructors
  , elem
  , fold
  , empty
  , siblings
  -- Convenience combinators
  , forEach
  , forEachP
  , forEachWithGUP
  , fromTree
  , preserveTree
  -- Finally tagless projection
  , class Project
  , project
  , MapKeys(..)
  , MapValues(..)
  , MapEntries(..)
  -- Behavior combinators
  , withBehaviors
  -- Attr constructors (for use inside templates)
  , staticStr
  , staticNum
  , thunkedStr
  , thunkedNum
  -- Behavior constructors (for use inside templates)
  , onMouseEnter
  , onMouseLeave
  , onClick
  , onDrag
  , onZoom
  -- Coordinated highlighting
  , module ReExportHighlight
  , onCoordinatedHighlight
  , onCoordinatedHighlightWithTooltip
  -- Coordinated interaction (brush + highlight)
  -- Note: Import InteractionTrigger, InteractionState, BoundingBox
  -- from Hylograph.Interaction.Coordinated if you need them for custom respond functions
  , onCoordinatedInteraction
  , onBrush
  ) where

import Prelude

import Data.Array as Array
import Data.Array (nub)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), snd)
import Effect (Effect)
import Hylograph.Internal.Selection.Types (ElementType(..))
import Hylograph.Internal.Behavior.Types (DragConfig, ZoomConfig, HighlightClass(..), TooltipTrigger(..)) as ReExportHighlight
import Hylograph.Internal.Behavior.Types (DragConfig, ZoomConfig, HighlightClass(..), TooltipTrigger(..))
import Hylograph.Interaction.Coordinated (InteractionTrigger(..), InteractionState(..), BoundingBox)
import Hylograph.Internal.Transition.Types (TransitionConfig)

-- ============================================================================
-- Core AST (Unparameterized)
-- ============================================================================

-- | The HATS tree type - a specification for visual structure.
-- |
-- | **No type parameter** - trees compose freely with `<>` regardless of
-- | what data they bind internally.
-- |
-- | Only three constructors:
-- | - `Elem` - A DOM element with attributes, children, and behaviors
-- | - `MkFold` - An existentially-wrapped iteration (enumerate, transform, assemble)
-- | - `Empty` - Nothing to render
data Tree
  = Elem
      { elemType :: ElementType
      , attrs :: Array Attr
      , children :: Array Tree
      , behaviors :: Array ThunkedBehavior
      }

  | MkFold SomeFold

  | Empty

-- | Semigroup instance: trees combine as siblings
-- |
-- | This enables compositional chart building:
-- | ```purescript
-- | chart = title <> xAxis <> yAxis <> plotArea <> legend
-- | ```
-- |
-- | **Key feature**: linksLayer <> nodesLayer works even when they
-- | bind different data types internally!
instance Semigroup Tree where
  append Empty t = t
  append t Empty = t
  append t1 t2 = siblings [t1, t2]

-- | Monoid instance with Empty as identity
instance Monoid Tree where
  mempty = Empty

-- ============================================================================
-- Existential Fold (CPS encoding)
-- ============================================================================

-- | Existentially-wrapped Fold specification.
-- |
-- | The datum type `a` is scoped to the Fold - it doesn't appear in
-- | the outer `Tree` type. This allows heterogeneous composition.
-- |
-- | Uses CPS encoding since PureScript doesn't have native existentials:
-- | `SomeFold` packs a `FoldSpec a` and can only be consumed by a
-- | polymorphic continuation that works for any `a`.
newtype SomeFold = SomeFold (forall r. (forall a. FoldSpec a -> r) -> r)

-- | Create a SomeFold from a FoldSpec (existentially packs the type)
mkSomeFold :: forall a. FoldSpec a -> SomeFold
mkSomeFold spec = SomeFold (\k -> k spec)

-- | Consume a SomeFold with a polymorphic handler
runSomeFold :: forall r. SomeFold -> (forall a. FoldSpec a -> r) -> r
runSomeFold (SomeFold f) k = f k

-- | Fold specification with its datum type.
-- |
-- | The `template` function receives a datum and returns a `Tree`.
-- | Inside the template, attributes and behaviors capture the datum
-- | via closures - the datum is "baked in" at template evaluation time.
type FoldSpec a =
  { name :: String                    -- Selection name for retrieval
  , elementType :: ElementType        -- Element type for GUP scoping
  , enumerate :: Enumeration a        -- How to get elements from input
  , assemble :: Assembly              -- How to structure output
  , keyFn :: a -> String              -- Identity function for diffing
  , template :: a -> Tree             -- How to visualize one element
  , gup :: Maybe (GUPSpec a)          -- Optional enter/update/exit
  }

-- ============================================================================
-- Attributes (Thunked)
-- ============================================================================

-- | Attribute type - either static or a thunk (closure).
-- |
-- | Thunked attributes capture their datum value at construction time.
-- | The interpreter just invokes the thunk to get the value.
data Attr
  = StaticAttr String String          -- name, value
  | ThunkedAttr String (Unit -> String)  -- name, thunk that produces value

-- ============================================================================
-- Behaviors (Thunked)
-- ============================================================================

-- | Behavior type with thunked handlers.
-- |
-- | Handlers are closures that capture datum values.
-- | The interpreter invokes them without needing to know the datum type.
data ThunkedBehavior
  = ThunkedMouseEnter (Unit -> Effect Unit)
  | ThunkedMouseLeave (Unit -> Effect Unit)
  | ThunkedClick (Unit -> Effect Unit)
  | ThunkedDrag DragConfig
  | ThunkedZoom ZoomConfig
  | ThunkedCoordinatedHighlight
      { identify :: Unit -> String           -- Thunked: captures datum, returns identity
      , classify :: String -> HighlightClass -- Curried: takes hoveredId, uses captured datum
      , group :: Maybe String                -- Optional group name for scoping
      , tooltipContent :: Maybe (Unit -> String)  -- Thunked tooltip content generator
      , tooltipTrigger :: TooltipTrigger          -- When to show tooltip
      }
  | ThunkedCoordinatedInteraction
      { identify :: Unit -> String                         -- Thunked: element identity
      , respond :: InteractionTrigger -> InteractionState  -- How to respond to any trigger
      , position :: Maybe (Unit -> { x :: Number, y :: Number })  -- For brush hit-testing
      , group :: Maybe String
      }
  | ThunkedBrush
      { extent :: BoundingBox                -- Brushable area
      , group :: Maybe String                -- Group to emit triggers to
      }

-- ============================================================================
-- Enumeration (Coalgebra - how to unfold/traverse input)
-- ============================================================================

-- | How to extract elements from a data structure.
data Enumeration a
  = FromArray (Array a)
  | FromTree
      { root :: a
      , children :: a -> Array a
      , order :: TraversalOrder
      , includeInternal :: Boolean
      }
  | WithContext (Array { datum :: a, depth :: Int, index :: Int })

-- | Traversal order for tree enumeration
data TraversalOrder
  = DepthFirst
  | BreadthFirst

-- ============================================================================
-- Assembly (Algebra - how to fold/structure output)
-- ============================================================================

-- | How to structure the output DOM.
data Assembly
  = Siblings  -- All elements as siblings at the same level
  | Nested    -- Preserve input structure in output

-- ============================================================================
-- GUP (General Update Pattern)
-- ============================================================================

-- | Specification for differential updates (enter/update/exit).
type GUPSpec a =
  { enter :: Maybe (PhaseSpec a)
  , update :: Maybe (PhaseSpec a)
  , exit :: Maybe (PhaseSpec a)
  }

-- | Specification for one phase of GUP
type PhaseSpec a =
  { attrs :: Array Attr  -- Note: uses thunked Attr now
  , transition :: Maybe TransitionConfig
  }

-- ============================================================================
-- Smart Constructors
-- ============================================================================

-- | Create an element node
elem
  :: ElementType
  -> Array Attr
  -> Array Tree
  -> Tree
elem elemType attrs children = Elem
  { elemType
  , attrs
  , children
  , behaviors: []
  }

-- | Create a fold node from a spec
fold :: forall a. FoldSpec a -> Tree
fold spec = MkFold (mkSomeFold spec)

-- | Empty tree
empty :: Tree
empty = Empty

-- | Combine multiple trees as siblings
siblings :: Array Tree -> Tree
siblings trees =
  case flatten trees of
    [] -> Empty
    [t] -> t
    ts -> Elem
      { elemType: Group
      , attrs: []
      , children: ts
      , behaviors: []
      }
  where
  flatten :: Array Tree -> Array Tree
  flatten = Array.concatMap \t -> case t of
    Empty -> []
    Elem e
      | e.elemType == Group
      , Array.null e.attrs
      , Array.null e.behaviors
      -> flatten e.children
    _ -> [t]

-- ============================================================================
-- Convenience Combinators
-- ============================================================================

-- | Simple iteration over an array (most common case)
-- |
-- | The datum type `a` is inferred from `items` and available in
-- | the template function. Use attr constructors that capture values:
-- |
-- | ```purescript
-- | forEach "circles" Circle points _.id \pt ->
-- |   elem Circle
-- |     [ thunkedNum "cx" pt.x
-- |     , thunkedNum "cy" pt.y
-- |     , staticNum "r" 5.0
-- |     ] []
-- | ```
forEach
  :: forall a
   . String                    -- Name
  -> ElementType               -- Element type for scoping
  -> Array a                   -- Data
  -> (a -> String)             -- Key function
  -> (a -> Tree)               -- Template (datum captured in closures)
  -> Tree
forEach name elementType items keyFn template = MkFold $ mkSomeFold
  { name
  , elementType
  , enumerate: FromArray items
  , assemble: Siblings
  , keyFn
  , template
  , gup: Nothing
  }

-- | Iteration with GUP (enter/update/exit transitions)
forEachWithGUP
  :: forall a
   . String
  -> ElementType
  -> Array a
  -> (a -> String)
  -> (a -> Tree)
  -> GUPSpec a
  -> Tree
forEachWithGUP name elementType items keyFn template gupSpec = MkFold $ mkSomeFold
  { name
  , elementType
  , enumerate: FromArray items
  , assemble: Siblings
  , keyFn
  , template
  , gup: Just gupSpec
  }

-- | Unfold a tree structure to flat output
fromTree
  :: forall a
   . String
  -> ElementType
  -> a
  -> (a -> Array a)
  -> (a -> String)
  -> TraversalOrder
  -> Boolean
  -> (a -> Tree)
  -> Tree
fromTree name elementType root children keyFn order includeInternal template = MkFold $ mkSomeFold
  { name
  , elementType
  , enumerate: FromTree { root, children, order, includeInternal }
  , assemble: Siblings
  , keyFn
  , template
  , gup: Nothing
  }

-- | Unfold a tree structure preserving hierarchy in output
preserveTree
  :: forall a
   . String
  -> ElementType
  -> a
  -> (a -> Array a)
  -> (a -> String)
  -> (a -> Tree)
  -> Tree
preserveTree name elementType root children keyFn template = MkFold $ mkSomeFold
  { name
  , elementType
  , enumerate: FromTree { root, children, order: DepthFirst, includeInternal: true }
  , assemble: Nested
  , keyFn
  , template
  , gup: Nothing
  }

-- ============================================================================
-- Finally Tagless Projection
-- ============================================================================

-- | Project a source structure into an array of target elements.
-- |
-- | The functional dependency `source -> target` ensures each source type
-- | has a canonical projection. Use newtypes for multiple projections from
-- | the same underlying type.
-- |
-- | This is "finally tagless" because:
-- | - The type class is open for extension - users can add new instances
-- | - Multiple projections from one source use newtypes to select
-- | - The story: "One Map, three views, one diagram"
class Project source target | source -> target where
  project :: source -> Array target

-- | Arrays project to their elements (identity projection)
instance projectArray :: Project (Array a) a where
  project = identity

-- ============================================================================
-- Map Projections (Multiple views of the same Map)
-- ============================================================================

-- | Project a Map to its keys
-- |
-- | Use when you want to iterate over just the keys:
-- | ```purescript
-- | forEachP "keys" Circle (MapKeys myMap) show \key -> ...
-- | ```
newtype MapKeys k v = MapKeys (Map k v)

-- | Project a Map to its unique values
-- |
-- | Values are deduplicated - if multiple keys map to the same value,
-- | that value appears only once. This is the mathematical codomain.
newtype MapValues k v = MapValues (Map k v)

-- | Project a Map to its key-value entries
-- |
-- | Each entry is a `Tuple k v` representing one mapping.
newtype MapEntries k v = MapEntries (Map k v)

instance projectMapKeys :: Ord k => Project (MapKeys k v) k where
  project (MapKeys m) = Array.fromFoldable (Map.keys m)

instance projectMapValues :: (Ord k, Ord v) => Project (MapValues k v) v where
  project (MapValues m) = nub $ map snd $ Map.toUnfoldable m

instance projectMapEntries :: Ord k => Project (MapEntries k v) (Tuple k v) where
  project (MapEntries m) = Map.toUnfoldable m

-- | forEach with projection - iterates over any Projectable source
-- |
-- | The killer feature: one Map, three projections, one diagram.
-- |
-- | ```purescript
-- | mapDiagram :: Map k v -> Tree
-- | mapDiagram m =
-- |   elem SVG [...]
-- |     [ -- Domain nodes from keys
-- |       forEachP "keys" Group (MapKeys m) show \key -> keyNode key
-- |
-- |     -- Codomain nodes from values (auto-deduplicated)
-- |     , forEachP "values" Group (MapValues m) show \value -> valueNode value
-- |
-- |     -- Arrows from entries
-- |     , forEachP "arrows" Path (MapEntries m) (\(Tuple k _) -> show k) \(Tuple k v) ->
-- |         arrow (keyPos k) (valuePos v)
-- |     ]
-- | ```
forEachP
  :: forall source target
   . Project source target
  => String                    -- Name
  -> ElementType               -- Element type for scoping
  -> source                    -- Any Projectable source
  -> (target -> String)        -- Key function
  -> (target -> Tree)          -- Template
  -> Tree
forEachP name elementType source keyFn template =
  forEach name elementType (project source) keyFn template

-- ============================================================================
-- Behavior Combinators
-- ============================================================================

-- | Attach behaviors to an element
withBehaviors :: Array ThunkedBehavior -> Tree -> Tree
withBehaviors bs = case _ of
  Elem spec -> Elem spec { behaviors = spec.behaviors <> bs }
  MkFold someFold -> runSomeFold someFold \spec ->
    MkFold $ mkSomeFold spec
      { template = \datum -> withBehaviors bs (spec.template datum) }
  Empty -> Empty

-- ============================================================================
-- Attr Constructors
-- ============================================================================

-- | Static string attribute (value known at build time)
staticStr :: String -> String -> Attr
staticStr name value = StaticAttr name value

-- | Static numeric attribute
staticNum :: String -> Number -> Attr
staticNum name value = StaticAttr name (show value)

-- | Thunked string attribute (captures a value)
-- |
-- | Use inside templates to capture datum-derived values:
-- | ```purescript
-- | \node -> elem Text [ thunkedStr "text-anchor" node.anchor ] []
-- | ```
thunkedStr :: String -> String -> Attr
thunkedStr name value = ThunkedAttr name (\_ -> value)

-- | Thunked numeric attribute (captures a value)
-- |
-- | Use inside templates to capture datum-derived values:
-- | ```purescript
-- | \node -> elem Circle [ thunkedNum "cx" node.x, thunkedNum "cy" node.y ] []
-- | ```
thunkedNum :: String -> Number -> Attr
thunkedNum name value = ThunkedAttr name (\_ -> show value)

-- ============================================================================
-- Behavior Constructors
-- ============================================================================

-- | Mouse enter handler (captures handler in closure)
-- |
-- | ```purescript
-- | \node -> withBehaviors [ onMouseEnter (callbacks.onHover node.path) ] $
-- |          elem Circle [...] []
-- | ```
onMouseEnter :: Effect Unit -> ThunkedBehavior
onMouseEnter handler = ThunkedMouseEnter (\_ -> handler)

-- | Mouse leave handler
onMouseLeave :: Effect Unit -> ThunkedBehavior
onMouseLeave handler = ThunkedMouseLeave (\_ -> handler)

-- | Click handler
onClick :: Effect Unit -> ThunkedBehavior
onClick handler = ThunkedClick (\_ -> handler)

-- | Drag behavior
onDrag :: DragConfig -> ThunkedBehavior
onDrag = ThunkedDrag

-- | Zoom behavior
onZoom :: ZoomConfig -> ThunkedBehavior
onZoom = ThunkedZoom

-- | Coordinated highlighting behavior
-- |
-- | When this element is hovered, ALL elements with coordinated highlighting
-- | in the same group receive CSS classes based on their relationship:
-- | - `.highlight-primary` - the hovered element itself
-- | - `.highlight-related` - elements related to hovered
-- | - `.highlight-dimmed` - unrelated elements
-- |
-- | Use inside forEach templates to capture datum:
-- | ```purescript
-- | forEach "nodes" Circle nodes _.id \node ->
-- |   withBehaviors
-- |     [ onCoordinatedHighlight
-- |         { identify: node.name
-- |         , classify: \hoveredId ->
-- |             if node.name == hoveredId then Primary
-- |             else if hoveredId `elem` node.connections then Related
-- |             else Dimmed
-- |         , group: Nothing  -- global coordination
-- |         , tooltip: Nothing  -- or Just { content: "...", showWhen: OnHover }
-- |         }
-- |     ] $
-- |   elem Circle [...] []
-- | ```
onCoordinatedHighlight
  :: { identify :: String
     , classify :: String -> HighlightClass
     , group :: Maybe String
     }
  -> ThunkedBehavior
onCoordinatedHighlight config = ThunkedCoordinatedHighlight
  { identify: \_ -> config.identify
  , classify: config.classify
  , group: config.group
  , tooltipContent: Nothing
  , tooltipTrigger: OnHover  -- Default, unused since tooltipContent is Nothing
  }

-- | Coordinated highlight with tooltip support
-- |
-- | Same as `onCoordinatedHighlight` but with optional tooltip configuration.
-- | When tooltip is provided, it will show on hover (or based on showWhen trigger).
-- |
-- | ```purescript
-- | forEach "nodes" Circle nodes _.id \node ->
-- |   withBehaviors
-- |     [ onCoordinatedHighlightWithTooltip
-- |         { identify: node.name
-- |         , classify: \hoveredId -> if node.name == hoveredId then Primary else Dimmed
-- |         , group: Nothing
-- |         , tooltip: Just { content: node.description, showWhen: OnHover }
-- |         }
-- |     ] $
-- |   elem Circle [...] []
-- | ```
onCoordinatedHighlightWithTooltip
  :: { identify :: String
     , classify :: String -> HighlightClass
     , group :: Maybe String
     , tooltip :: Maybe { content :: String, showWhen :: TooltipTrigger }
     }
  -> ThunkedBehavior
onCoordinatedHighlightWithTooltip config = ThunkedCoordinatedHighlight
  { identify: \_ -> config.identify
  , classify: config.classify
  , group: config.group
  , tooltipContent: (\t -> \_ -> t.content) <$> config.tooltip
  , tooltipTrigger: case config.tooltip of
      Just t -> t.showWhen
      Nothing -> OnHover  -- Default, but won't be used since tooltipContent is Nothing
  }

-- | Full coordinated interaction behavior (supports brush, hover, focus, selection)
-- |
-- | Unlike `onCoordinatedHighlight` which only handles hover,
-- | this behavior responds to ALL interaction triggers including brush regions.
-- |
-- | ```purescript
-- | forEach "points" Circle points _.id \pt ->
-- |   withBehaviors
-- |     [ onCoordinatedInteraction
-- |         { identify: pt.id
-- |         , respond: \trigger -> case trigger of
-- |             HoverTrigger id -> if pt.id == id then Primary else Dimmed
-- |             BrushTrigger box -> if pointInBox pt.pos box then Selected else Dimmed
-- |             ClearTrigger -> Neutral
-- |             _ -> Neutral
-- |         , position: Just pt.pos  -- For automatic brush hit-testing
-- |         , group: Nothing
-- |         }
-- |     ] $
-- |   elem Circle [...] []
-- | ```
onCoordinatedInteraction
  :: { identify :: String
     , respond :: InteractionTrigger -> InteractionState
     , position :: Maybe { x :: Number, y :: Number }
     , group :: Maybe String
     }
  -> ThunkedBehavior
onCoordinatedInteraction config = ThunkedCoordinatedInteraction
  { identify: \_ -> config.identify
  , respond: config.respond
  , position: (\pos -> \_ -> pos) <$> config.position  -- Thunk the position
  , group: config.group
  }

-- | Attach a brush overlay to an element
-- |
-- | When users brush (drag) on this element, a `BrushTrigger` is emitted
-- | to all elements registered with `onCoordinatedInteraction` in the same group.
-- |
-- | ```purescript
-- | elem Group [ staticStr "class" "brush-overlay" ] []
-- |   # withBehaviors
-- |       [ onBrush
-- |           { extent: { x0: 0.0, y0: 0.0, x1: 400.0, y1: 300.0 }
-- |           , group: Just "scatter-plot"
-- |           }
-- |       ]
-- | ```
onBrush
  :: { extent :: BoundingBox
     , group :: Maybe String
     }
  -> ThunkedBehavior
onBrush config = ThunkedBrush
  { extent: config.extent
  , group: config.group
  }
