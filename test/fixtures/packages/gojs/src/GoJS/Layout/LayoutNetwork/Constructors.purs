module GoJS.Layout.LayoutNetwork.Constructors where

import Effect (Effect)
import GoJS.Layout.Types (CircularNetwork_, ForceDirectedNetwork_, LayeredDigraphNetwork_, TreeNetwork_)
import GoJS.Unsafe (constructor0)

newCircularNetwork :: Effect CircularNetwork_
newCircularNetwork = constructor0 "CircularNetwork"

newForceDirectedNetwork :: Effect ForceDirectedNetwork_
newForceDirectedNetwork = constructor0 "ForceDirectedNetwork"

newLayeredDigraphNetwork :: Effect LayeredDigraphNetwork_
newLayeredDigraphNetwork = constructor0 "LayeredDigraphNetwork"

newTreeNetwork :: Effect TreeNetwork_
newTreeNetwork = constructor0 "TreeNetwork"