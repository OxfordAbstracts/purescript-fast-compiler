module VISX.Grid where

import Prelude
import React.Basic (ReactComponent)

foreign import gridColumnsImpl ∷ ∀ r. ReactComponent { | r }
foreign import gridRowsImpl ∷ ∀ r. ReactComponent { | r }
foreign import gridImpl ∷ ∀ r. ReactComponent { | r } 
foreign import gridRadialImpl ∷ ∀ r. ReactComponent { | r }
foreign import gridPolarImpl ∷ ∀ r. ReactComponent { | r }
foreign import gridAngleImpl ∷ ∀ r. ReactComponent { | r }