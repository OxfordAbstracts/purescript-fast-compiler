module VISX.Layout.Geo where

import Prelude
import React.Basic (ReactComponent)

foreign import mercatorImpl ∷ ∀ p. ReactComponent { | p }

foreign import graticuleImpl ∷ ∀ p. ReactComponent { | p }

foreign import equalEarthImpl ∷ ∀ p. ReactComponent { | p }

foreign import naturalEarthImpl ∷ ∀ p. ReactComponent { | p }

foreign import orthographicImpl ∷ ∀ p. ReactComponent { | p }

foreign import albersUsaImpl ∷ ∀ p. ReactComponent { | p }

foreign import albersImpl ∷ ∀ p. ReactComponent { | p }
