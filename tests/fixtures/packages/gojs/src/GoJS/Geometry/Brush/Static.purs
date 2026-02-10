module GoJS.Geometry.Brush.Static where

import Effect (Effect)
import GoJS.Unsafe (callStatic0, callStaticPure1, callStaticPure3)
import GoJS.EnumValue (EnumValue_)

darken_ :: String -> String
darken_ = callStaticPure1 "Brush" "darken"

-- Optional parameters: fraction: number, mode: EnumValue
darkenBy_ :: String -> Number -> EnumValue_ -> String
darkenBy_ = callStaticPure3 "Brush" "darkenBy"

isDark_ :: String -> Boolean
isDark_ = callStaticPure1 "Brush" "isDark"

isValidColor_ :: String -> Boolean
isValidColor_ = callStaticPure1 "Brush" "isValidColor"

lighten_ :: String -> String
lighten_ = callStaticPure1 "Brush" "lighten"

-- Optional parameters: fraction: number, mode: EnumValue
lightenBy_ :: String -> Number -> EnumValue_ -> String
lightenBy_ = callStaticPure3 "Brush" "lightenBy"

-- Optional parameters: fraction: number
mix_ :: String -> String -> Number -> String
mix_ = callStaticPure3 "Brush" "mix"

randomColor_ :: Effect String
randomColor_ = callStatic0 "Brush" "randomColor"