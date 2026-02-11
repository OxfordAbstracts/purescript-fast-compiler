-- | Some functions from the CSSOM spec that are useful for canvas code. These
-- | might move to another package in the future.
module Graphics.CanvasAction.CSSOM
  ( devicePixelRatio

  , MediaQueryList
  , fromEventTarget
  , toEventTarget
  , matchMedia

  , MediaQueryListEvent
  , fromEvent
  , toEvent
  ) where

import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Unsafe.Coerce (unsafeCoerce)
import Web.Event.Internal.Types (Event, EventTarget)
import Web.Internal.FFI (unsafeReadProtoTagged)

foreign import devicePixelRatioImpl ∷ Effect Number

devicePixelRatio ∷ ∀ m. MonadEffect m ⇒ m Number
devicePixelRatio = liftEffect devicePixelRatioImpl

foreign import data MediaQueryList ∷ Type

fromEventTarget ∷ EventTarget → Maybe MediaQueryList
fromEventTarget = unsafeReadProtoTagged "MediaQueryList"

toEventTarget ∷ MediaQueryList → EventTarget
toEventTarget = unsafeCoerce

foreign import matchMedia ∷ String → Effect MediaQueryList

foreign import data MediaQueryListEvent ∷ Type

fromEvent ∷ Event → Maybe MediaQueryListEvent
fromEvent = unsafeReadProtoTagged "MediaQueryListEvent"

toEvent ∷ MediaQueryListEvent → Event
toEvent = unsafeCoerce
