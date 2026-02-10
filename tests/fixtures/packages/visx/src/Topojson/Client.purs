module Topojson.Client where

import Prelude
import Data.Function.Uncurried (Fn2, runFn2)
import Foreign (Foreign)

type Features a =
  { type ∷ FeatureCollection, features ∷ Array a }

type FeatureCollection =
  {}

foreign import featureImpl ∷ ∀ feature. Fn2 Foreign String (Features feature)

feature ∷ ∀ a. Foreign -> String -> { features ∷ Array a, type ∷ Record () }
feature = runFn2 featureImpl
