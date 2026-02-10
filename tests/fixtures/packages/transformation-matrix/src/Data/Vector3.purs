module Data.TransformationMatrix.Vector3 where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray, cons')
import Data.Either (Either)
import Data.Foldable (class Foldable, foldr, foldl, foldMap)
import Data.Generic.Rep (class Generic)
import Data.Number (sqrt)
import Data.Show.Generic (genericShow)
import Data.Traversable (class Traversable)
import Data.TransformationMatrix.Division (divide)
import Data.TransformationMatrix.DivisionError (DivisionError)

data Vector3 a = Vector3 a a a

derive instance genericVector3 :: Generic (Vector3 a) _

instance showVector3 :: Show a => Show (Vector3 a) where
  show = genericShow

derive instance eqVector3 :: Eq a => Eq (Vector3 a)

derive instance ordVector3 :: Ord a => Ord (Vector3 a)

instance functorVector3 :: Functor Vector3 where
  map f (Vector3 x1 x2 x3) =
    Vector3
      (f x1)
      (f x2)
      (f x3)

instance foldableVector3 :: Foldable Vector3 where
  foldr f e (Vector3 x1 x2 x3) = foldr f e [ x1, x2, x3 ]
  foldl f e (Vector3 x1 x2 x3) = foldl f e [ x1, x2, x3 ]
  foldMap f (Vector3 x1 x2 x3) = foldMap f [ x1, x2, x3 ]

instance traversableVector3 :: Traversable Vector3 where
  traverse f (Vector3 x1 x2 x3) = Vector3 <$> f x1 <*> f x2 <*> f x3
  sequence (Vector3 m1 m2 m3) = Vector3 <$> m1 <*> m2 <*> m3

toNonEmptyArray :: forall a. Vector3 a -> NonEmptyArray a
toNonEmptyArray (Vector3 x1 x2 x3) = cons' x1 [ x2, x3 ]

toArray :: forall a. Vector3 a -> Array a
toArray (Vector3 x1 x2 x3) = [ x1, x2, x3 ]

lengthSquared
  :: Vector3 Number
  -> Number
lengthSquared (Vector3 x y z) = (x * x) + (y * y) + (z * z)

length
  :: Vector3 Number
  -> Number
length v3 = (sqrt <<< lengthSquared) v3

subtract
  :: Vector3 Number
  -> Vector3 Number
  -> Vector3 Number
subtract (Vector3 x1 y1 z1) (Vector3 x2 y2 z2) = Vector3 (x1 - x2) (y1 - y2) (z1 - z2)

add
  :: Vector3 Number
  -> Vector3 Number
  -> Vector3 Number
add (Vector3 x1 y1 z1) (Vector3 x2 y2 z2) = Vector3 (x1 + x2) (y1 + y2) (z1 + z2)

dotProduct
  :: Vector3 Number
  -> Vector3 Number
  -> Number
dotProduct (Vector3 x1 y1 z1) (Vector3 x2 y2 z2) = (x1 * x2) + (y1 * y2) + (z1 * z2)

crossProduct
  :: Vector3 Number
  -> Vector3 Number
  -> Vector3 Number
crossProduct (Vector3 x1 y1 z1) (Vector3 x2 y2 z2) = Vector3 x y z
  where
  x = (y1 * z2) - (z1 * y2)
  y = (z1 * x2) - (x1 * z2)
  z = (x1 * y2) - (y1 * x2)

divideByScalar
  :: Number
  -> Vector3 Number
  -> Either DivisionError (Vector3 Number)
divideByScalar scalar (Vector3 x y z) = Vector3
  <$> (divide x scalar)
  <*> (divide y scalar)
  <*> (divide z scalar)

multiplyByScalar
  :: Number
  -> Vector3 Number
  -> Vector3 Number
multiplyByScalar scalar (Vector3 x y z) = (Vector3 (scalar * x) (scalar * y) (scalar * z))

normalize
  :: Vector3 Number
  -> Either DivisionError (Vector3 Number)
normalize v = divideByScalar (length v) v

distanceBetweenSquared
  :: Vector3 Number
  -> Vector3 Number
  -> Number
distanceBetweenSquared v1 v2 = lengthSquared $ subtract v1 v2
