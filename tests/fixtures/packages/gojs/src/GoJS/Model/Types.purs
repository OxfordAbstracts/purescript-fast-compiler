module GoJS.Model.Types where

foreign import data Binding_ :: Type
foreign import data ChangedEvent_ :: Type
foreign import data Transaction_ :: Type
foreign import data UndoManager_ :: Type

-- | Model types.
foreign import data Model_ :: Row Type -> Type
foreign import data TreeModel_ :: Row Type -> Type
foreign import data GraphLinksModel_ :: Row Type -> Row Type -> Type

class IsModel (d :: Type)
instance IsModel (Model_ nodeData)
instance IsModel (TreeModel_ nodeData)
instance IsModel (GraphLinksModel_ linkData nodeData)
