module NaturalTransformationAlias where

-- Tests capture-avoiding substitution when a type alias introduces a forall
-- whose bound variable name clashes with an outer type parameter.
-- Without alpha-renaming, `a ~> b` incorrectly expands to `forall a. a a -> b a`.

type NatTrans f g = forall a. f a -> g a

data Box a = Box a

unbox :: forall a. Box a -> a
unbox (Box x) = x

-- The outer `a` and `b` clash with the forall variable `a` inside NatTrans.
mapBox :: forall a b. NatTrans a b -> Box (a Int) -> Box (b Int)
mapBox nat (Box x) = Box (nat x)
