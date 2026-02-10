module Yoga.WebBoss where

import Prelude

import Effect (Effect)
import Yoga.WebProletarian.Types (Worker)

foreign import onMessageFromWorker
  ∷ ∀ toWorker toBoss. (toBoss → Effect Unit) → Worker toWorker toBoss → Effect Unit

foreign import postMessageToWorker ∷ ∀ toBoss toWorker. toWorker → Worker toWorker toBoss → Effect Unit

foreign import terminate ∷ ∀ toWorker toBoss. Worker toWorker toBoss → Effect Unit
