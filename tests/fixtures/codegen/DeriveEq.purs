module DeriveEq where

import Prelude

-- Simple enum
data Color = Red | Green | Blue

derive instance eqColor :: Eq Color

-- Data with fields
data Pair a b = Pair a b

derive instance eqPair :: (Eq a, Eq b) => Eq (Pair a b)

-- Single constructor with multiple fields
data Point = Point Int Int

derive instance eqPoint :: Eq Point

-- Mix of nullary and non-nullary constructors
data Maybe a = Nothing | Just a

derive instance eqMaybe :: Eq a => Eq (Maybe a)

test = Just (Pair 1 2) == Just (Pair 1 2)

-- TEST: true
