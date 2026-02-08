module Web.HTML.Window.AnimationFrame where

import Prelude

import Effect (Effect)
import Web.HTML.Window (RequestAnimationFrameId, Window)

newtype DOMHighResTimestamp = DOMHighResTimestamp Number

foreign import requestAnimationFrame :: (DOMHighResTimestamp -> Effect Unit) -> Window -> Effect RequestAnimationFrameId
