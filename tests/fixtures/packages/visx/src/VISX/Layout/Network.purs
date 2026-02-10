module VISX.Layout.Network where

import React.Basic (ReactComponent)

foreign import graphImpl ∷ ∀ p. ReactComponent p
foreign import nodesImpl ∷ ∀ p. ReactComponent p
foreign import linksImpl ∷ ∀ p. ReactComponent p
foreign import defaultNodeImpl ∷ ∀ p. ReactComponent p
foreign import defaultLinksImpl ∷ ∀ p. ReactComponent p
