module VISX.Legend where

import Prelude
import React.Basic (ReactComponent)

foreign import legendImpl ∷ ∀ r. ReactComponent { | r }
foreign import legendLegend ∷ ∀ r. ReactComponent { | r }
foreign import legendLabelImpl ∷ ∀ r. ReactComponent { | r }
foreign import legendLinearImpl ∷ ∀ r. ReactComponent { | r }
foreign import legendOrdinalImpl ∷ ∀ r. ReactComponent { | r }
foreign import legendQuantileImpl ∷ ∀ r. ReactComponent { | r }
foreign import legendShapeImpl ∷ ∀ r. ReactComponent { | r }
foreign import legendSizeImpl ∷ ∀ r. ReactComponent { | r }
foreign import legendThresholdImpl ∷ ∀ r. ReactComponent { | r }
foreign import lineShapeImpl ∷ ∀ r. ReactComponent { | r }
foreign import rectShapeImpl ∷ ∀ r. ReactComponent { | r }
