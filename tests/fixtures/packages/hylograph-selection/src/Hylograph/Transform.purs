-- | Generic element transformation based on bound data
-- |
-- | Provides a type-safe way to update attributes on DOM elements
-- | based on their D3-bound data. Used for animations and position updates.
-- |
-- | Example:
-- | ```purescript
-- | -- Update circle positions during animation
-- | transformCircles "#viz" \node ->
-- |   { cx: lerp 0.0 node.treeX progress
-- |   , cy: lerp 0.0 node.treeY progress
-- |   }
-- |
-- | -- Update line positions
-- | transformLines "#viz" \link ->
-- |   { x1: lerp 0.0 link.sourceX progress
-- |   , y1: lerp 0.0 link.sourceY progress
-- |   , x2: lerp 0.0 link.targetX progress
-- |   , y2: lerp 0.0 link.targetY progress
-- |   }
-- | ```
module Hylograph.Transform
  ( transformCircles
  , transformLines
  , transformPaths
  , transformGroups
  , transformGroupsById
  , transformGroupsByName
  , setGroupsOpacityById
  , setViewBox
  , clearContainer
  , removeElement
  , CirclePosition
  , LinePosition
  , Point
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toNullable)
import Effect (Effect)

-- | Point position for group transforms
type Point =
  { x :: Number
  , y :: Number
  }

-- | Position for circle elements
type CirclePosition =
  { cx :: Number
  , cy :: Number
  }

-- | Position for line elements
type LinePosition =
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  }

-- | Transform circle elements by updating cx/cy based on bound data
-- |
-- | For each circle matching the selector, calls the transformer function
-- | with the element's bound data and updates the cx/cy attributes.
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for the container (e.g., "#viz")
-- | - `transformer`: Function from bound data to CirclePosition
-- |
-- | The phantom type `d` ensures type safety - the transformer must accept
-- | the same data type that was bound to the elements.
foreign import transformCircles_
  :: forall d
   . String                    -- Container selector
  -> (d -> CirclePosition)     -- Transformer function
  -> Effect Unit

-- | Transform line elements by updating x1/y1/x2/y2 based on bound data
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for the container (e.g., "#viz")
-- | - `transformer`: Function from bound data to LinePosition
foreign import transformLines_
  :: forall d
   . String                    -- Container selector
  -> (d -> LinePosition)       -- Transformer function
  -> Effect Unit

-- | Transform circle elements by updating cx/cy based on bound data
transformCircles
  :: forall d
   . String                    -- Container selector
  -> (d -> CirclePosition)     -- Transformer function
  -> Effect Unit
transformCircles = transformCircles_

-- | Transform line elements by updating x1/y1/x2/y2 based on bound data
transformLines
  :: forall d
   . String                    -- Container selector
  -> (d -> LinePosition)       -- Transformer function
  -> Effect Unit
transformLines = transformLines_

-- | Transform path elements by updating d attribute based on bound data
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for the container (e.g., "#viz")
-- | - `transformer`: Function from bound data to path d string
foreign import transformPaths_
  :: forall d
   . String                    -- Container selector
  -> (d -> String)             -- Transformer function returning path d
  -> Effect Unit

-- | Transform path elements by updating d attribute based on bound data
transformPaths
  :: forall d
   . String                    -- Container selector
  -> (d -> String)             -- Transformer function returning path d
  -> Effect Unit
transformPaths = transformPaths_

-- | Clear all child elements from a container
foreign import clearContainer_ :: String -> Effect Unit

-- | Clear all child elements from a container
clearContainer :: String -> Effect Unit
clearContainer = clearContainer_

-- | Remove an element from the DOM entirely
foreign import removeElement_ :: String -> Effect Unit

-- | Remove an element from the DOM entirely
removeElement :: String -> Effect Unit
removeElement = removeElement_

-- | Transform group elements by updating transform attribute based on bound data
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for the container (e.g., "#viz")
-- | - `groupSelector`: CSS selector for groups within container (e.g., ".node-group")
-- | - `transformer`: Function from bound data to transform string (e.g., "translate(x, y)")
foreign import transformGroups_
  :: forall d
   . String                    -- Container selector
  -> String                    -- Group selector
  -> (d -> String)             -- Transformer function returning transform string
  -> Effect Unit

-- | Transform group elements by updating transform attribute based on bound data
transformGroups
  :: forall d
   . String                    -- Container selector
  -> String                    -- Group selector
  -> (d -> String)             -- Transformer function returning transform string
  -> Effect Unit
transformGroups = transformGroups_

-- | Transform groups by ID lookup: update transform using a position lookup function
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for the container
-- | - `groupSelector`: CSS selector for groups within container
-- | - `idAttr`: Attribute name containing the ID (e.g., "data-id")
-- | - `lookupFn`: Function from ID to Point or Nothing
foreign import transformGroupsById_
  :: String                    -- Container selector
  -> String                    -- Group selector
  -> String                    -- ID attribute name
  -> (Int -> Nullable Point)   -- Position lookup function
  -> Effect Unit

-- | Transform groups by ID lookup: update transform using a position lookup function
transformGroupsById
  :: String                    -- Container selector
  -> String                    -- Group selector
  -> String                    -- ID attribute name
  -> (Int -> Maybe Point)      -- Position lookup function
  -> Effect Unit
transformGroupsById container group idAttr lookupFn =
  transformGroupsById_ container group idAttr (toNullable <<< lookupFn)

-- | Transform groups by NAME lookup: update transform using a position lookup function
-- |
-- | This variant is useful when matching between different data sources by name.
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for the container
-- | - `groupSelector`: CSS selector for groups within container
-- | - `nameAttr`: Attribute name containing the name (e.g., "data-name")
-- | - `lookupFn`: Function from name String to Point or Nothing
foreign import transformGroupsByName_
  :: String                    -- Container selector
  -> String                    -- Group selector
  -> String                    -- Name attribute name
  -> (String -> Nullable Point) -- Position lookup function
  -> Effect Unit

-- | Transform groups by NAME lookup: update transform using a position lookup function
transformGroupsByName
  :: String                    -- Container selector
  -> String                    -- Group selector
  -> String                    -- Name attribute name
  -> (String -> Maybe Point)   -- Position lookup function
  -> Effect Unit
transformGroupsByName container group nameAttr lookupFn =
  transformGroupsByName_ container group nameAttr (toNullable <<< lookupFn)

-- | Set opacity on groups by ID lookup
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for the container
-- | - `groupSelector`: CSS selector for groups within container
-- | - `idAttr`: Attribute name containing the ID
-- | - `lookupFn`: Function from ID to opacity or Nothing
foreign import setGroupsOpacityById_
  :: String                    -- Container selector
  -> String                    -- Group selector
  -> String                    -- ID attribute name
  -> (Int -> Nullable Number)  -- Opacity lookup function
  -> Effect Unit

-- | Set opacity on groups by ID lookup
setGroupsOpacityById
  :: String                    -- Container selector
  -> String                    -- Group selector
  -> String                    -- ID attribute name
  -> (Int -> Maybe Number)     -- Opacity lookup function
  -> Effect Unit
setGroupsOpacityById container group idAttr lookupFn =
  setGroupsOpacityById_ container group idAttr (toNullable <<< lookupFn)

-- | Set viewBox on an SVG element
-- |
-- | Parameters:
-- | - `containerSelector`: CSS selector for container with SVG
-- | - `minX`, `minY`: ViewBox origin
-- | - `width`, `height`: ViewBox dimensions
foreign import setViewBox_
  :: String -> Number -> Number -> Number -> Number -> Effect Unit

-- | Set viewBox on an SVG element
setViewBox :: String -> Number -> Number -> Number -> Number -> Effect Unit
setViewBox = setViewBox_
