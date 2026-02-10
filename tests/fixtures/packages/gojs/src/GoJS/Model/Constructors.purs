module GoJS.Model.Constructors where

import Effect (Effect)
import GoJS.Model.Types (Model_)
import GoJS.Unsafe (constructor0)

newModel :: forall nodeData. Effect (Model_ nodeData)
newModel = constructor0 "Model"