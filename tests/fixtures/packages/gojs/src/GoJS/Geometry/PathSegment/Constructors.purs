module GoJS.Geometry.PathSegment.Constructors where

import GoJS.Geometry.Types (PathSegment_)

foreign import pathSegmentLine_ :: Number -> Number -> PathSegment_
foreign import pathSegmentQuadraticBezier_ :: Number -> Number -> Number -> Number -> PathSegment_
foreign import pathSegmentBezier_ :: Number -> Number -> Number -> Number -> Number -> Number -> PathSegment_
foreign import pathSegmentArc_ :: Number -> Number -> Number -> Number -> Number -> Number -> PathSegment_
foreign import pathSegmentSvgArc_ :: Number -> Number -> Number -> Number -> Number -> Number -> Boolean -> PathSegment_
foreign import pathSegmentMove_ :: Number -> Number -> PathSegment_
foreign import close_ :: PathSegment_ -> PathSegment_
