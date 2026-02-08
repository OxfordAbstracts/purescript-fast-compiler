module GoJS.Geometry.PathFigure.Constructors where

import GoJS.Geometry.Types (PathFigure_)

foreign import pathFigure_ :: forall r. Number -> Number -> Boolean -> Boolean -> Boolean -> Array r -> PathFigure_

