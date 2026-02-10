module GoJS.GraphObject.Picture.PictureElement where

import Unsafe.Coerce (unsafeCoerce)
import Web.HTML (HTMLCanvasElement, HTMLImageElement, HTMLVideoElement)

foreign import whichPictureElementStr :: forall k. k -> String

data PictureElement
  = Canvas HTMLCanvasElement
  | Image HTMLImageElement
  | Video HTMLVideoElement
  | Unknown

whichPictureElement :: forall k. k -> PictureElement
whichPictureElement k = case whichPictureElementStr k of
  "canvas" -> Canvas (unsafeCoerce k)
  "image" ->  Image (unsafeCoerce k)
  "video" ->  Video (unsafeCoerce k)
  _ -> Unknown