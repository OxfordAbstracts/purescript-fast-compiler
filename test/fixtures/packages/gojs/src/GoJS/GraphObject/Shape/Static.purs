module GoJS.GraphObject.Shape.Static where

import Prelude

import Data.Function.Uncurried (Fn3)
import Effect (Effect)
import GoJS.Collection (Map_)
import GoJS.Geometry.Types (Geometry_)
import GoJS.GraphObject.Types (Shape_)
import GoJS.Unsafe (callStatic0, callStatic2)

defineArrowheadGeometry_ :: String -> Geometry_ -> Effect Unit
defineArrowheadGeometry_ = callStatic2 "Shape" "defineArrowheadGeometry"

defineFigureGenerator_ :: String -> (Fn3 Shape_ Number Number Geometry_) -> Effect Unit
defineFigureGenerator_ = callStatic2 "Shape" "defineFigureGenerator"

getArrowheadGeometries_ :: Effect (Map_ String Geometry_)
getArrowheadGeometries_ = callStatic0 "Shape" "getArrowheadGeometries"

getFigureGenerators_ :: Effect (Map_ String (Fn3 Shape_ Number Number Geometry_))
getFigureGenerators_ = callStatic0 "Shape" "getFigureGenerators"
