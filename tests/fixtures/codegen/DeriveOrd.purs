module DeriveOrd where

import Prelude (class Eq, class Ord)

data Ordering = LT | EQ | GT

data Color = Red | Green | Blue

derive instance eqColor :: Eq Color
derive instance ordColor :: Ord Color

data Maybe a = Nothing | Just a

derive instance eqMaybe :: Eq a => Eq (Maybe a)
derive instance ordMaybe :: Ord a => Ord (Maybe a)

-- No runtime test: local Ordering type conflicts with Prelude's
