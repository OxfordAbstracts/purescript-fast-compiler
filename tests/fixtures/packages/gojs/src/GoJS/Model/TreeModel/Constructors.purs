module GoJS.Model.TreeModel.Constructors where

import Effect (Effect)
import GoJS.Model.Types (TreeModel_)
import GoJS.Unsafe (constructor0)

newTreeModel :: forall nodeData. Effect (TreeModel_ nodeData)
newTreeModel = constructor0 "TreeModel"