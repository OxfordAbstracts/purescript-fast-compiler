module GoJS.Model.GraphLinksModel.Constructors where

import Effect (Effect)
import GoJS.Model.Types (GraphLinksModel_)
import GoJS.Unsafe (constructor0)

newGraphLinksModel :: forall nodeData linkData. Effect (GraphLinksModel_ nodeData linkData)
newGraphLinksModel = constructor0 "GraphLinksModel"