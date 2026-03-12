module DeriveOrd where

class Eq a where
  eq :: a -> a -> Boolean

class Eq a <= Ord a where
  compare :: a -> a -> Ordering

data Ordering = LT | EQ | GT

data Color = Red | Green | Blue

derive instance eqColor :: Eq Color
derive instance ordColor :: Ord Color

data Maybe a = Nothing | Just a

derive instance eqMaybe :: Eq a => Eq (Maybe a)
derive instance ordMaybe :: Ord a => Ord (Maybe a)
