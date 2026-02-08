module GoJS.Diagram.Layer.Methods where

import Prelude

import Data.Function.Uncurried (Fn1)
import Data.Maybe (Maybe)
import Data.Nullable (toMaybe)
import Effect (Effect)
import GoJS.Collection (List_)
import GoJS.Diagram.Types (Layer_)
import GoJS.Geometry.Types (Point_, Rect_)
import GoJS.GraphObject.Types (class IsGraphObject)
import GoJS.Unsafe (callUnsafe3, callUnsafe4, callUnsafe5)

-- Optional parameters: navig: (a: GraphObject) => T, pred: (a: T) => boolean
findObjectAt_ :: forall g t. IsGraphObject g => IsGraphObject t => Point_ -> Fn1 g t -> Fn1 t Boolean -> Layer_ -> Effect (Maybe t)
findObjectAt_ p f pred x = toMaybe <$> callUnsafe3 "findObjectAt" p f pred x

-- Optional parameters: p: Point, navig: (a: GraphObject) => T, pred: (a: T) => boolean, coll: S
findObjectsAt_ :: forall g t. IsGraphObject g => IsGraphObject t => Point_ -> Fn1 g t -> Fn1 t Boolean -> Layer_ -> Effect (List_ t)
findObjectsAt_ p f pred x = callUnsafe3 "findObjectsAt" p f pred x

-- Optional parameters: r: Rect, navig: (a: GraphObject) => T, pred: (a: T) => boolean, partialInclusion: boolean, coll: S
findObjectsIn_ :: forall g t. IsGraphObject g => IsGraphObject t => Rect_ -> Fn1 g t -> Fn1 t Boolean -> Boolean -> Layer_ -> Effect (List_ t)
findObjectsIn_ p f pred x = callUnsafe4 "findObjectsIn" p f pred x

-- Optional parameters: p: Point, dist: number, navig: (a: GraphObject) => T, pred: (a: T) => boolean, partialInclusion: boolean, coll: S
findObjectsNear_ :: forall g t. IsGraphObject g => IsGraphObject t => Point_ -> Number -> Fn1 g t -> Fn1 t Boolean -> Boolean -> Layer_ -> Effect (List_ t)
findObjectsNear_ p dist f pred partialInclusion x = callUnsafe5 "findObjectsNear" p dist f pred partialInclusion x