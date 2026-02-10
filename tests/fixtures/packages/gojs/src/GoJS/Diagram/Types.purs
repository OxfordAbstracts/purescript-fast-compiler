module GoJS.Diagram.Types where

import Data.Function.Uncurried (Fn4)

-- | Diagram types
foreign import data Diagram_ :: Type
foreign import data Palette_ :: Type
foreign import data Overview_ :: Type
class IsDiagram (d :: Type)

instance IsDiagram Diagram_
instance IsDiagram Palette_
instance IsDiagram Overview_

-- TODO: Rethink how to establish diagram type polymorphism
foreign import data DiagramEvent_ :: Type -> Type
foreign import data InputEvent_ :: Type -> Type
foreign import data DraggingInfo_ :: Type
foreign import data DraggingOptions_ :: Type

foreign import data Layer_ :: Type
foreign import data Animation_ :: Type
foreign import data AnimationManager_ :: Type
foreign import data AnimationTrigger_ :: Type

type EasingFunction = Fn4 Number Number Number Number Number