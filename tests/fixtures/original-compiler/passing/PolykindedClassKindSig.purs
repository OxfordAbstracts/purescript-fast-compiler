module Main where

-- Polykinded data type with explicit kind signature
data List' :: forall k. k -> Type
data List' k

foreign import data Nil' :: forall k. List' k
foreign import data Cons' :: forall k. k -> List' k -> List' k

-- Classes with forall k kind sigs where k only appears inside List' k
-- (k's kind is fully polymorphic — not ambiguous)
class Concat :: forall k. List' k -> List' k -> List' k -> Constraint
class Concat xs ys zs | xs ys -> zs

class IsEmpty :: forall k. List' k -> Boolean -> Constraint
class IsEmpty xs r | xs -> r

class Init :: forall k. List' k -> List' k -> Constraint
class Init xs ys | xs -> ys

-- Class where k appears both directly and inside List' k
class IsMember :: forall k. k -> List' k -> Constraint
class IsMember x xs | x xs -> x

-- Polykinded data declaration
data ListProxy :: forall k. List' k -> Type
data ListProxy l = ListProxy
