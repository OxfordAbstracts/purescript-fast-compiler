module GoJS.Geometry.Spot where

import GoJS.Geometry.Types (Spot_)

foreign import newSpot :: forall x y offx offy. x -> y -> offx -> offy -> Spot_
foreign import topSide_ :: Spot_
foreign import topBottomSides_ :: Spot_
foreign import topLeftSides_ :: Spot_
foreign import topRightSides_ :: Spot_
foreign import bottomSide_ :: Spot_
foreign import bottomLeftSides_ :: Spot_
foreign import bottomRightSides_ :: Spot_
foreign import leftRightSides_ :: Spot_
foreign import leftSide_ :: Spot_
foreign import rightSide_ :: Spot_