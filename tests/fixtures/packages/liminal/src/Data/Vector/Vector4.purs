module Data.Vector.Vector4 where

import Prelude
import Data.Traversable (class Traversable)
import Data.Foldable (class Foldable, foldr, foldl, foldMap)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Array.NonEmpty (NonEmptyArray, cons')

data Vector4 a = Vector4 a a a a

derive instance genericVector4 :: Generic (Vector4 a) _

instance showVector4 :: Show a => Show (Vector4 a) where
  show = genericShow

derive instance eqVector4 :: Eq a => Eq (Vector4 a)

instance functorVector4 :: Functor Vector4 where
  map f (Vector4 x1 x2 x3 x4) =
    Vector4
      (f x1)
      (f x2)
      (f x3)
      (f x4)

instance foldableVector4 :: Foldable Vector4 where
  foldr f e (Vector4 x1 x2 x3 x4) = foldr f e [ x1, x2, x3, x4 ]
  foldl f e (Vector4 x1 x2 x3 x4) = foldl f e [ x1, x2, x3, x4 ]
  foldMap f (Vector4 x1 x2 x3 x4) = foldMap f [ x1, x2, x3, x4 ]

instance traversableVector4 :: Traversable Vector4 where
  traverse f (Vector4 x1 x2 x3 x4) = Vector4
    <$> (f x1)
    <*> (f x2)
    <*> (f x3)
    <*> (f x4)
  sequence (Vector4 m1 m2 m3 m4) = Vector4
    <$> m1
    <*> m2
    <*> m3
    <*> m4

toNonEmptyArray :: forall a. Vector4 a -> NonEmptyArray a
toNonEmptyArray (Vector4 x1 x2 x3 x4) = cons' x1 [ x2, x3, x4 ]

toArray :: forall a. Vector4 a -> Array a
toArray (Vector4 x1 x2 x3 x4) = [ x1, x2, x3, x4 ]
