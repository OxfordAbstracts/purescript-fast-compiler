module Yoga.Tree.Svg.Geometry
    ( findPosition
    , rotateBy
    , Position, Size, Positioned
    , transform, scale
    ) where

import Prelude

import Data.Int (toNumber) as Int
import Data.Number (cos, sin) as Number


findPosition :: Number -> Position -> Number -> Number -> Int -> Int -> Position
findPosition baseDistance parent startAngle endAngle count index =
    let
        currentAngle = startAngle + ((endAngle - startAngle) / Int.toNumber count) * Int.toNumber index

        co = Number.cos currentAngle
        si = Number.sin currentAngle

        x = parent.x + (co * baseDistance - si * baseDistance)
        y = parent.y + (si * baseDistance + co * baseDistance)
    in
    { x, y }


rotateBy :: Position -> Position -> Number -> Number -> Position
rotateBy parent current scaleFactor theta =
    let
        dx = current.x - parent.x
        dy = current.y - parent.y
        co = Number.cos theta
        si = Number.sin theta
        xx = parent.x + scaleFactor * (co * dx - si * dy)
        yy = parent.y + scaleFactor * (si * dx + co * dy)
    in
    { x : xx, y : yy }


type Position = { x :: Number, y :: Number }
type Size = { width :: Number, height :: Number }
type Positioned a = { x :: Number, y :: Number, width :: Number, height :: Number, value :: a }


transform :: forall a. Number -> Number -> Number -> Number -> Positioned a -> Positioned a
transform dx dy sx sy node =
    node { x = sx * node.x + dx, y = sy * node.y + dy, width = sx * node.width, height = sy * node.height }


scale :: forall a. Number -> Positioned a -> Positioned a
scale factor =
    transform 0.0 0.0 factor factor
