module GoJS.Geometry.Brush.BrushPattern where

import Unsafe.Coerce (unsafeCoerce)
import Web.HTML (HTMLCanvasElement, HTMLImageElement)

foreign import whichBrushPatternStr :: forall k. k -> String

-- TODO: See GoJS.GraphObject.Picture.PictureElement. It's a superset
-- of this type - would be nice if we could *build* variant types compositionally
-- with regular pattern matching (on strings in both cases).
data BrushPattern
  = Canvas HTMLCanvasElement
  | Image HTMLImageElement
  | Unknown

whichBrushPattern :: forall k. k -> BrushPattern
whichBrushPattern k = case whichBrushPatternStr k of
  "canvas" -> Canvas (unsafeCoerce k)
  "image" ->  Image (unsafeCoerce k)
  _ -> Unknown