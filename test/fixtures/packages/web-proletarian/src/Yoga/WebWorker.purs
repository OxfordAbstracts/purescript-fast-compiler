module Yoga.WebWorker where

import Prelude
import Effect (Effect)

foreign import subscribe :: forall toWorker. (toWorker -> Effect Unit) -> Effect Unit

foreign import quit :: Effect Unit

foreign import postMessageToBoss :: forall toBoss. toBoss -> Effect Unit

