module GoJS.Tool.MouseUpTools.ClickCreatingTool.Methods where

import Effect (Effect)
import GoJS.GraphObject.Types (class IsPart)
import GoJS.Tool.Types (ClickCreatingTool_)
import GoJS.Unsafe (callUnsafe1)

insertPart_ :: forall p. IsPart p => p -> ClickCreatingTool_ -> Effect p
insertPart_ = callUnsafe1 "insertPart"