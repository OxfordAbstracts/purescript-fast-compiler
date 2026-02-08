module GoJS.Tool.MouseUpTools.ContextMenuTool.Methods where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.Diagram (class IsDiagram)
import GoJS.GraphObject.Types (class IsGraphObject, Adornment_, ContextMenu_(..))
import GoJS.Tool.Types (ContextMenuTool_)
import GoJS.Unsafe (callUnsafe0, callUnsafe1, callUnsafe2)

-- findObjectWithContextMenu_ is split into the two functions below, so that the return type is the
-- same as the input.
findGraphObjectWithContextMenu_ :: forall g. IsGraphObject g => g -> ContextMenuTool_ -> Effect (Maybe g)
findGraphObjectWithContextMenu_ obj t = toMaybe <$> callUnsafe1 "findObjectWithContextMenu" obj t

findDiagramWithContextMenu_ :: forall d. IsDiagram d => d -> ContextMenuTool_ -> Effect (Maybe d)
findDiagramWithContextMenu_ diag t = toMaybe <$> callUnsafe1 "findObjectWithContextMenu" diag t

hideContextMenu_ :: ContextMenuTool_ -> Effect Unit
hideContextMenu_ = callUnsafe0 "hideContextMenu"

hideDefaultContextMenu_ :: ContextMenuTool_ -> Effect Unit
hideDefaultContextMenu_ = callUnsafe0 "hideDefaultContextMenu"

positionContextMenu_ :: forall g. IsGraphObject g => Adornment_ -> g -> ContextMenuTool_ -> Effect Unit
positionContextMenu_ = callUnsafe2 "positionContextMenu"

showContextMenu_ :: forall g. IsGraphObject g => ContextMenu_ -> g -> ContextMenuTool_ -> Effect Unit
showContextMenu_ contextmenu obj t = case contextmenu of
  AdornmentContextMenu adornment ->  callUnsafe2 "showContextMenu" adornment obj t
  HTMLInfoContextMenu htmlinfo ->  callUnsafe2 "showContextMenu" htmlinfo obj t

showDefaultContextMenu_ :: ContextMenuTool_ -> Effect Unit
showDefaultContextMenu_ = callUnsafe0 "showDefaultContextMenu"