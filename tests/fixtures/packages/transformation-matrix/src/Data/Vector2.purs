module Data.TransformationMatrix.Vector2 where

import Prelude
import Data.Traversable (class Traversable)
import Data.Foldable (class Foldable, foldr, foldl, foldMap)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Array.NonEmpty (NonEmptyArray, cons')
import Data.TransformationMatrix.Division (divide)
import Data.TransformationMatrix.DivisionError (DivisionError)
import Data.Either (Either)
import Data.Number (sqrt)

data Vector2 a = Vector2 a a

derive instance genericVector2 :: Generic (Vector2 a) _

instance showVector2 :: Show a => Show (Vector2 a) where
  show = genericShow

derive instance eqVector2 :: Eq a => Eq (Vector2 a)

instance functorVector2 :: Functor Vector2 where
  map f (Vector2 x1 x2) =
    Vector2
      (f x1)
      (f x2)

instance foldableVector2 :: Foldable Vector2 where
  foldr f e (Vector2 x1 x2) = foldr f e [ x1, x2 ]
  foldl f e (Vector2 x1 x2) = foldl f e [ x1, x2 ]
  foldMap f (Vector2 x1 x2) = foldMap f [ x1, x2 ]

instance traversableVector2 :: Traversable Vector2 where
  traverse f (Vector2 x1 x2) = Vector2
    <$> (f x1)
    <*> (f x2)

  sequence (Vector2 m1 m2) = Vector2
    <$> m1
    <*> m2

toNonEmptyArray :: forall a. Vector2 a -> NonEmptyArray a
toNonEmptyArray (Vector2 x1 x2) = cons' x1 [ x2 ]

toArray :: forall a. Vector2 a -> Array a
toArray (Vector2 x1 x2) = [ x1, x2 ]

subtractVector2s
  :: Vector2 Number
  -> Vector2 Number
  -> Vector2 Number
subtractVector2s (Vector2 x1 y1) (Vector2 x2 y2) = Vector2 (x1 - x2) (y1 - y2)

lengthSquared
  :: Vector2 Number
  -> Number
lengthSquared (Vector2 x y) = (x * x) + (y * y)

length
  :: Vector2 Number
  -> Number
length v = (sqrt <<< lengthSquared) v

vector2DistanceBetweenSquared
  :: Vector2 Number
  -> Vector2 Number
  -> Number
vector2DistanceBetweenSquared v1 v2 = lengthSquared $ subtractVector2s v1 v2

divideByScalar
  :: Number
  -> Vector2 Number
  -> Either DivisionError (Vector2 Number)
divideByScalar scalar (Vector2 x y) = Vector2
  <$> (divide x scalar)
  <*> (divide y scalar)