-- | Core Selection API
-- |
-- | Entry points for creating and querying DOM selections.
-- | These are the primary functions users interact with for data binding.
module Hylograph.Internal.Selection.Operations.Selection
  ( -- * Selection creation
    select
  , selectElement
  , selectAll
  , selectAllWithData
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, toMaybe)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Hylograph.Internal.Selection.Operations.Helpers (getDocument, querySelectorAllElements)
import Hylograph.Internal.Selection.Types (SBoundOwns, SEmpty, Selection(..), SelectionImpl(..), mkBoundSelection)
import Unsafe.Coerce (unsafeCoerce)
import Web.DOM.Element (Element)
import Web.DOM.ParentNode (QuerySelector(..), querySelector)
import Web.HTML (window)
import Web.HTML.HTMLDocument (toDocument)
import Web.HTML.HTMLDocument as HTMLDocument
import Web.HTML.Window (document)

-- =============================================================================
-- FFI
-- =============================================================================

-- | Get data from an element (D3-style __data__ property)
foreign import getElementData_ :: forall datum. Element -> Effect (Nullable datum)

-- =============================================================================
-- Selection Creation
-- =============================================================================

-- | Select a single element matching the CSS selector
-- |
-- | Returns an empty selection (no data bound).
-- | The datum type is polymorphic and will be inferred from usage.
-- | This is typically the starting point for data binding.
-- |
-- | Example:
-- | ```purescript
-- | svg <- select "svg"
-- | circles <- renderData Circle [1, 2, 3] "circle" svg ...
-- | ```
select
  :: forall m datum
   . MonadEffect m
  => String -- CSS selector
  -> m (Selection SEmpty Element datum)
select selector = liftEffect do
  htmlDoc <- window >>= document
  let doc = toDocument htmlDoc
  let parentNode = HTMLDocument.toParentNode htmlDoc
  maybeElement <- querySelector (QuerySelector selector) parentNode
  case maybeElement of
    Nothing -> pure $ Selection $ EmptySelection
      { parentElements: []
      , document: doc
      }
    Just element -> pure $ Selection $ EmptySelection
      { parentElements: [ element ]
      , document: doc
      }

-- | Select from a DOM element directly
-- |
-- | This is useful for framework integration (React, Vue, etc.) where you have
-- | a reference to a DOM element rather than a CSS selector.
-- |
-- | Example:
-- | ```purescript
-- | selectElement element >>= renderTree myVisualization
-- | ```
selectElement
  :: forall m datum
   . MonadEffect m
  => Element -- DOM element
  -> m (Selection SEmpty Element datum)
selectElement element = liftEffect do
  htmlDoc <- window >>= document
  let doc = toDocument htmlDoc
  pure $ Selection $ EmptySelection
    { parentElements: [ element ]
    , document: doc
    }

-- | Select all elements matching the CSS selector within a parent selection
-- |
-- | Returns an empty selection (no data bound yet).
-- | The datum type is polymorphic and will be inferred from usage.
-- | Use this for nested selections.
-- |
-- | Example:
-- | ```purescript
-- | svg <- select "svg"
-- | groups <- selectAll "g" svg
-- | ```
selectAll
  :: forall state parent parentDatum datum m
   . MonadEffect m
  => String -- CSS selector
  -> Selection state parent parentDatum
  -> m (Selection SEmpty Element datum)
selectAll _ (Selection impl) = liftEffect do
  doc <- getDocument impl
  -- Get the parent elements (where new children will be appended)
  -- NOT the query results - those are fetched by joinData when needed
  let
    parentElems = case impl of
      EmptySelection { parentElements } -> parentElements
      BoundSelection { elements } -> elements
      PendingSelection { parentElements } -> parentElements
      ExitingSelection { elements } -> elements

  pure $ Selection $ EmptySelection
    { parentElements: parentElems -- Preserve parents for appending
    , document: doc
    }

-- | Select all elements matching selector and extract their bound data
-- |
-- | Use this when selecting child elements that have inherited data from their parent.
-- | This is necessary when you want to use the selection with transitions that need
-- | access to the bound data (like withTransitionStaggered).
-- |
-- | Example:
-- | ```purescript
-- | -- After creating nodes with appendChildInheriting
-- | groups <- selectSimulationGroups
-- | circles <- selectAllWithData "circle" groups.nodes
-- | withTransitionStaggered config delayFn circles [fill colorByDepth]
-- | ```
selectAllWithData
  :: forall state parent parentDatum datum m
   . MonadEffect m
  => String -- CSS selector
  -> Selection state parent parentDatum
  -> m (Selection SBoundOwns Element datum)
selectAllWithData selector (Selection impl) = liftEffect do
  doc <- getDocument impl
  elements <- case impl of
    EmptySelection { parentElements } ->
      querySelectorAllElements selector parentElements
    BoundSelection { elements: parentElems } ->
      querySelectorAllElements selector parentElems
    PendingSelection { parentElements } ->
      querySelectorAllElements selector parentElements
    ExitingSelection { elements: exitElems } ->
      querySelectorAllElements selector exitElems

  -- Extract __data__ from each element
  dataArray <- traverse
    ( \el -> do
        nullableDatum <- getElementData_ el
        pure $ case toMaybe nullableDatum of
          Just d -> d
          Nothing -> unsafeCoerce unit -- Fallback if no data (shouldn't happen with appendChildInheriting)
    )
    elements

  pure $ mkBoundSelection elements dataArray Nothing doc
