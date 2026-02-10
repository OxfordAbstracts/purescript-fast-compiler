module GoJS.Tool.MouseDownTools.LinkReshapingTool.Properties where

import GoJS.Collection (List_)
import GoJS.Geometry.Types (Point_)
import GoJS.GraphObject.Types (class IsGraphObject, Link_)
import GoJS.Tool (LinkReshapingTool_)
import GoJS.Unsafe (getUnsafe)

-- Read-only
_adornedLink :: LinkReshapingTool_ -> Link_
_adornedLink = getUnsafe ["adornedLink"]

_handle :: forall @g. IsGraphObject g => LinkReshapingTool_ -> g
_handle = getUnsafe ["handle"]

_handleArchetype :: forall @g. IsGraphObject g => LinkReshapingTool_ -> g
_handleArchetype = getUnsafe ["handleArchetype"]

_midHandleArchetype :: forall @g. IsGraphObject g => LinkReshapingTool_ -> g
_midHandleArchetype = getUnsafe ["midHandleArchetype"]

-- Read-only
_originalPoint :: LinkReshapingTool_ -> Point_
_originalPoint = getUnsafe ["originalPoint"]

-- Read-only
_originalPoints :: LinkReshapingTool_ -> List_ Point_
_originalPoints = getUnsafe ["originalPoints"]

