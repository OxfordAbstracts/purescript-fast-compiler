-- | Types for geometric layout patterns
module DataViz.Layout.Pattern.Types
  ( Point
  , Viewport
  , viewport
  , viewportWithPadding
  , usableArea
  , Padding
  , uniformPadding
  , padding
  , noPadding
  ) where

import Prelude

-- | A 2D point
type Point = { x :: Number, y :: Number }

-- | Padding specification (can be uniform or per-side)
type Padding =
  { top :: Number
  , right :: Number
  , bottom :: Number
  , left :: Number
  }

-- | Uniform padding on all sides
uniformPadding :: Number -> Padding
uniformPadding p = { top: p, right: p, bottom: p, left: p }

-- | Per-side padding
padding :: { top :: Number, right :: Number, bottom :: Number, left :: Number } -> Padding
padding = identity

-- | No padding
noPadding :: Padding
noPadding = { top: 0.0, right: 0.0, bottom: 0.0, left: 0.0 }

-- | Viewport specification - the bounding box for layout
type Viewport =
  { width :: Number
  , height :: Number
  , padding :: Padding
  }

-- | Create a viewport with no padding
viewport :: Number -> Number -> Viewport
viewport w h = { width: w, height: h, padding: noPadding }

-- | Create a viewport with uniform padding
viewportWithPadding :: Number -> Number -> Number -> Viewport
viewportWithPadding w h p = { width: w, height: h, padding: uniformPadding p }

-- | Get the usable area after accounting for padding
-- | Returns { x, y, width, height } where x,y is the top-left of usable area
usableArea :: Viewport -> { x :: Number, y :: Number, width :: Number, height :: Number }
usableArea vp =
  { x: vp.padding.left
  , y: vp.padding.top
  , width: vp.width - vp.padding.left - vp.padding.right
  , height: vp.height - vp.padding.top - vp.padding.bottom
  }
