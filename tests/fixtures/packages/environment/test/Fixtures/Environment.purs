module Test.Fixtures.Environment where

import Prelude

import Effect.Class (class MonadEffect, liftEffect)
import Node.Process (setEnv, unsetEnv)
import PointFree ((<..))

set ∷ ∀ m. MonadEffect m ⇒ String → String → m Unit
set = liftEffect <.. setEnv

unset ∷ ∀ m. MonadEffect m ⇒ String → m Unit
unset = liftEffect <<< unsetEnv
