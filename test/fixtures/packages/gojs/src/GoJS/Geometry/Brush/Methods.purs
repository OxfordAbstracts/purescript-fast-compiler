module GoJS.Geometry.Brush.Methods where


import Effect (Effect)
import GoJS.EnumValue (EnumValue_)
import GoJS.Geometry.Types (Brush_)
import GoJS.Unsafe (callUnsafe0, callUnsafe2)


addColorStop_ :: Number -> String -> Brush_ -> Effect Brush_
addColorStop_ = callUnsafe2 "addColorStop"

copy_ :: Brush_ -> Effect Brush_
copy_ = callUnsafe0 "copy"

-- Optional parameters: fraction: number, mode: EnumValue
darkenBy_ :: Number -> EnumValue_ -> Brush_ -> Effect Brush_
darkenBy_ = callUnsafe2 "darkenBy"

isDark_ :: Brush_ -> Effect Boolean
isDark_ = callUnsafe0 "isDark"

-- Optional parameters: fraction: number, mode: EnumValue
lightenBy_ :: Number -> EnumValue_ -> Brush_ -> Effect Brush_
lightenBy_ = callUnsafe2 "lightenBy"