module GoJS.Tool.MouseDownTools.RotatingTool.Properties where

import GoJS.Geometry.Types (Point_)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Tool.Types (RotatingTool_)
import GoJS.Unsafe (getUnsafe)

_adornedObject :: forall g. IsGraphObject g => RotatingTool_ -> g
_adornedObject = getUnsafe ["adornedObject"]

_handle :: forall g. IsGraphObject g => RotatingTool_ -> g
_handle = getUnsafe ["handle"]

_handleAngle :: RotatingTool_ -> Number
_handleAngle = getUnsafe ["handleAngle"]

_handleArchetype :: forall g. IsGraphObject g => RotatingTool_ -> g
_handleArchetype = getUnsafe ["handleArchetype"]

_handleDistance :: RotatingTool_ -> Number
_handleDistance = getUnsafe ["handleDistance"]

_originalAngle :: RotatingTool_ -> Number
_originalAngle = getUnsafe ["originalAngle"]

_rotationPoint :: RotatingTool_ -> Point_
_rotationPoint = getUnsafe ["rotationPoint"]

_snapAngleEpsilon :: RotatingTool_ -> Number
_snapAngleEpsilon = getUnsafe ["snapAngleEpsilon"]

_snapAngleMultiple :: RotatingTool_ -> Number
_snapAngleMultiple = getUnsafe ["snapAngleMultiple"]