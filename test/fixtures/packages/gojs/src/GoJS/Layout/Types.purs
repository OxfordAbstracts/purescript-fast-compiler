module GoJS.Layout.Types where

foreign import data Layout_ :: Type
foreign import data GridLayout_ :: Type
foreign import data CircularLayout_ :: Type
foreign import data ForceDirectedLayout_ :: Type
foreign import data LayeredDigraphLayout_ :: Type
foreign import data TreeLayout_ :: Type

class IsLayout (a :: Type)

-- Layout is an abstract, base class. No instance for it models this here.
instance IsLayout GridLayout_
instance IsLayout CircularLayout_
instance IsLayout ForceDirectedLayout_
instance IsLayout LayeredDigraphLayout_
instance IsLayout TreeLayout_

-- | Layout network types.
class IsLayoutNetwork (a :: Type)
class IsLayoutEdge (a :: Type)
class IsLayoutVertex (a :: Type)

foreign import data CircularNetwork_ :: Type
foreign import data ForceDirectedNetwork_ :: Type
foreign import data LayeredDigraphNetwork_ :: Type
foreign import data TreeNetwork_ :: Type

instance IsLayoutNetwork CircularNetwork_
instance IsLayoutNetwork ForceDirectedNetwork_
instance IsLayoutNetwork LayeredDigraphNetwork_
instance IsLayoutNetwork TreeNetwork_

foreign import data CircularEdge_ :: Type
foreign import data ForceDirectedEdge_ :: Type
foreign import data LayeredDigraphEdge_ :: Type
foreign import data TreeEdge_ :: Type

instance IsLayoutEdge CircularEdge_
instance IsLayoutEdge ForceDirectedEdge_
instance IsLayoutEdge LayeredDigraphEdge_
instance IsLayoutEdge TreeEdge_

foreign import data CircularVertex_ :: Type
foreign import data ForceDirectedVertex_ :: Type
foreign import data LayeredDigraphVertex_ :: Type
foreign import data TreeVertex_ :: Type

instance IsLayoutVertex CircularVertex_
instance IsLayoutVertex ForceDirectedVertex_
instance IsLayoutVertex LayeredDigraphVertex_
instance IsLayoutVertex TreeVertex_

-- | Four-way relation of layout, network, edge, and vertex types.
class (IsLayout l, IsLayoutNetwork n, IsLayoutEdge e, IsLayoutVertex v) <= LayoutNetwork (l :: Type) (n :: Type) (e :: Type) (v :: Type) | l -> n e v, n -> l e v, e -> l n v, v -> l n e

instance LayoutNetwork CircularLayout_ CircularNetwork_ CircularEdge_ CircularVertex_
instance LayoutNetwork ForceDirectedLayout_ ForceDirectedNetwork_ ForceDirectedEdge_ ForceDirectedVertex_
instance LayoutNetwork LayeredDigraphLayout_ LayeredDigraphNetwork_ LayeredDigraphEdge_ LayeredDigraphVertex_
instance LayoutNetwork TreeLayout_ TreeNetwork_ TreeEdge_ TreeVertex_
