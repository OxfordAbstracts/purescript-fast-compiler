module GoJS.Class where

import Data.Symbol (class IsSymbol)
import GoJS.Diagram.Types (Diagram_, Overview_, Palette_)
import GoJS.Tool.Types (ActionTool_, ClickCreatingTool_, ClickSelectingTool_, ContextMenuTool_, DragSelectingTool_, DraggingTool_, LinkReshapingTool_, LinkingTool_, PanningTool_, RelinkingTool_, ResizingTool_, RotatingTool_, TextEditingTool_)
import GoJS.Layout.Types (CircularLayout_, ForceDirectedLayout_, GridLayout_, LayeredDigraphLayout_, TreeLayout_)
import GoJS.Model.Types (GraphLinksModel_, Model_, TreeModel_)

-- | Typeclass for extracting a GoJS class name from an opaque type.
class ClassName :: forall k. k -> Symbol -> Constraint
class IsSymbol name <= ClassName t (name :: Symbol) | t -> name, name -> t

instance ClassName Diagram_ "Diagram"
instance ClassName Palette_ "Palette"
instance ClassName Overview_ "Overview"

instance ClassName (Model_ nodeData) "Model"
instance ClassName (TreeModel_ nodeData) "TreeModel"
instance ClassName (GraphLinksModel_ linkData nodeData) "GraphLinksModel"

instance ClassName GridLayout_ "GridLayout"
instance ClassName CircularLayout_ "CircularLayout"
instance ClassName ForceDirectedLayout_ "ForceDirectedLayout"
instance ClassName LayeredDigraphLayout_ "LayeredDigraphLayout"
instance ClassName TreeLayout_ "TreeLayout"

instance ClassName ClickCreatingTool_ "ClickCreatingTool"
instance ClassName ActionTool_ "ActionTool"
instance ClassName ClickSelectingTool_ "ClickSelectingTool"
instance ClassName ContextMenuTool_ "ContextMenuTool"
instance ClassName DragSelectingTool_ "DragSelectingTool"
instance ClassName DraggingTool_ "DraggingTool"
instance ClassName LinkReshapingTool_ "LinkReshapingTool"
instance ClassName LinkingTool_ "LinkingTool"
instance ClassName PanningTool_ "PanningTool"
instance ClassName RelinkingTool_ "RelinkingTool"
instance ClassName ResizingTool_ "ResizingTool"
instance ClassName RotatingTool_ "RotatingTool"
instance ClassName TextEditingTool_ "TextEditingTool"