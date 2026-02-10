module Data.Vector.Polymorphic
  ( length
  , diagonal
  , inside
  , outside
  , putInsideMod
  , area
  , perimeter
  , ratio
  , midPos
  , dot
  , perpendicular
  , parallel
  , convertPos
  , convertSize
  , convertRegion

  , module Types
  ) where

import Prelude

import Data.Vector.Polymorphic.Types (Rect(..), (><))
import Data.Vector.Polymorphic.Types (Rect(..), Vector2(..), (><), getX, getY, getPos, getSize, makeRect) as Types
import Data.Vector.Polymorphic.Class (class AsPosEndo, class FromPos, class FromRegion, class FromSize, class ToPos, class ToRegion, class ToSize, asPosEndo, fromPos, fromRegion, fromSize, toPos, toRegion, toSize)
import Data.Number (sqrt)

-- | Get the length of a position vector
length ∷ ∀ p. ToPos Number p ⇒ p → Number
length = toPos >>> \(x >< y) → sqrt (x * x + y * y)

-- | Get the diagonal of a size
diagonal ∷ ∀ s. ToSize Number s ⇒ s → Number
diagonal = toSize >>> \(w >< h) → sqrt (w * w + h * h)

-- | Checks if a position is inside a region. Size of the region should be
-- | positive. Inclusive on the lower bound, exclusive on the higher bound.
inside
  ∷ ∀ r p n. ToRegion n r ⇒ ToPos n p ⇒ Ord n ⇒ Semiring n ⇒ r → p → Boolean
inside region pos = case toRegion region, toPos pos of
  Rect (rx >< ry) (rw >< rh), (x >< y)
    | x < rx → false
    | x >= rx + rw → false
    | y < ry → false
    | y >= ry + rh → false
    | otherwise → true

-- | `inside`, but with its result negated.
outside
  ∷ ∀ r p n. ToRegion n r ⇒ ToPos n p ⇒ Ord n ⇒ Semiring n ⇒ r → p → Boolean
outside = not inside

-- | Put a position inside a region by using the modulus operator
putInsideMod
  ∷ ∀ r p n. ToRegion n r ⇒ AsPosEndo n p ⇒ EuclideanRing n ⇒ r → p → p
putInsideMod inputRect = asPosEndo \inputPos → ado
  rpos ← rectPos
  rsize ← rectSize
  pos ← inputPos
  in ((pos - rpos) `mod` rsize) + rpos
  where
  (Rect rectPos rectSize) = toRegion inputRect

-- | Get the area of a size
area ∷ ∀ s n. ToSize n s ⇒ Semiring n ⇒ s → n
area = toSize >>> \(w >< h) → w * h

-- | Get the perimeter of a size
perimeter ∷ ∀ s n. ToSize n s ⇒ Semiring n ⇒ s → n
perimeter = toSize >>> \(w >< h) → (w + w + h + h)

-- | Get the ratio of a size by dividing the width by the height
ratio ∷ ∀ s n. ToSize n s ⇒ EuclideanRing n ⇒ s → n
ratio = toSize >>> \(w >< h) → w / h

-- | Get the center position of a region
midPos ∷ ∀ s p n. ToRegion n s ⇒ FromPos n p ⇒ EuclideanRing n ⇒ s → p
midPos region = fromPos $ (\p s → p + half s) <$> pos <*> size
  where
  (Rect pos size) = toRegion region
  half n = n / (one + one)

-- | Get the dot product of two vectors
dot ∷ ∀ p n. ToPos n p ⇒ Semiring n ⇒ p → p → n
dot p1 p2 = x1 * x2 + y1 * y2
  where
  (x1 >< y1) = toPos p1
  (x2 >< y2) = toPos p2

-- | Check if two vectors are perpendicular
perpendicular ∷ ∀ p n. ToPos n p ⇒ Semiring n ⇒ Eq n ⇒ p → p → Boolean
perpendicular p1 p2 = dot p1 p2 == zero

-- | Check if two vectors are parallel
parallel ∷ ∀ p n. ToPos n p ⇒ EuclideanRing n ⇒ Eq n ⇒ p → p → Boolean
parallel p1 p2 = case toPos p1, toPos p2 of
  (x1 >< y1), (x2 >< y2)
    | y1 == zero || y2 == zero → y1 == y2
    | otherwise → x1 / y1 == x2 / y2

convertPos ∷ ∀ p1 p2 n. ToPos n p1 ⇒ FromPos n p2 ⇒ p1 → p2
convertPos = fromPos <<< toPos

convertSize ∷ ∀ p1 p2 n. ToSize n p1 ⇒ FromSize n p2 ⇒ p1 → p2
convertSize = fromSize <<< toSize

convertRegion ∷ ∀ p1 p2 n. ToRegion n p1 ⇒ FromRegion n p2 ⇒ p1 → p2
convertRegion = fromRegion <<< toRegion
