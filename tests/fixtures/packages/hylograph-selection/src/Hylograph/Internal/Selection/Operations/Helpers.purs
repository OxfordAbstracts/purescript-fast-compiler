-- | DOM Helper Functions for Selection Operations
-- |
-- | Low-level utilities for DOM queries and element creation.
-- | These are used throughout the selection operations but have minimal dependencies.
module Hylograph.Internal.Selection.Operations.Helpers
  ( -- * Document access
    getDocument
    -- * Element creation
  , createElementWithNS
    -- * DOM queries
  , querySelectorAllElements
  , queryFirstChild
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Hylograph.Internal.Selection.Operations.Conversions (elementTypeToString)
import Hylograph.Internal.Selection.Types (ElementType, RenderContext(..), SelectionImpl(..), elementContext)
import Web.DOM.Document (Document)
import Web.DOM.Document as Document
import Web.DOM.Element (Element, fromNode, toParentNode)
import Web.DOM.NodeList as NodeList
import Web.DOM.ParentNode (QuerySelector(..), querySelector, querySelectorAll)

-- =============================================================================
-- Document Access
-- =============================================================================

-- | Extract the Document from any SelectionImpl
getDocument :: forall parent datum. SelectionImpl parent datum -> Effect Document
getDocument (EmptySelection { document: doc }) = pure doc
getDocument (BoundSelection { document: doc }) = pure doc
getDocument (PendingSelection { document: doc }) = pure doc
getDocument (ExitingSelection { document: doc }) = pure doc

-- =============================================================================
-- Element Creation
-- =============================================================================

-- | Create an element with the appropriate namespace
-- | Uses the element's rendering context to determine namespace
createElementWithNS :: ElementType -> Document -> Effect Element
createElementWithNS elemType doc =
  case elementContext elemType of
    SVGContext ->
      -- SVG elements need the SVG namespace
      Document.createElementNS (Just "http://www.w3.org/2000/svg") (elementTypeToString elemType) doc
    HTMLContext ->
      -- HTML elements use default namespace
      Document.createElement (elementTypeToString elemType) doc

-- =============================================================================
-- DOM Queries
-- =============================================================================

-- | Query all matching elements within parent elements
-- | Uses web-dom library functions instead of custom FFI
querySelectorAllElements :: String -> Array Element -> Effect (Array Element)
querySelectorAllElements selector parents = do
  -- Convert each parent to ParentNode and query
  nodeArrays <- parents # traverse \parent -> do
    let parentNode = toParentNode parent
    nodeList <- querySelectorAll (QuerySelector selector) parentNode
    nodes <- NodeList.toArray nodeList
    -- Filter and convert Nodes to Elements
    pure $ Array.mapMaybe fromNode nodes
  -- Flatten the array of arrays
  pure $ Array.concat nodeArrays

-- | Query first matching child element within a parent
-- | Like querySelector but for a single Element parent
queryFirstChild :: String -> Element -> Effect (Maybe Element)
queryFirstChild selector parent = do
  let parentNode = toParentNode parent
  querySelector (QuerySelector selector) parentNode
