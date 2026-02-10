module GoJS.Tool.MouseDownTools.RelinkingTool.Properties where


import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Tool.Types (RelinkingTool_)
import GoJS.Unsafe (getUnsafe)

_fromHandleArchetype :: forall @g. IsGraphObject g => RelinkingTool_ -> g
_fromHandleArchetype = getUnsafe ["fromHandleArchetype"]

_handle :: forall @g. IsGraphObject g => RelinkingTool_ -> g
_handle = getUnsafe ["handle"]

_toHandleArchetype :: forall @g. IsGraphObject g => RelinkingTool_ -> g
_toHandleArchetype = getUnsafe ["toHandleArchetype"]