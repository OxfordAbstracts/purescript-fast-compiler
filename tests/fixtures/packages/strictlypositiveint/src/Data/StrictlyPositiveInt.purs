-- | A data type for representing positive integers not including zero.

module Data.StrictlyPositiveInt
    ( StrictlyPositiveInt()
    , fromInt
    , toInt
    , minus
    , plus
    , one
    ) where

import Prelude

newtype StrictlyPositiveInt = Private_ Int

-- | If i is less than one, returns one.
fromInt :: Int -> StrictlyPositiveInt
fromInt i = Private_ (if i >= 1 then i else 1)

toInt :: StrictlyPositiveInt -> Int
toInt (Private_ i) = i

-- | Subtract a StrictlyPositiveInt from another, with the result lower-bounded
-- | by one.
minus :: StrictlyPositiveInt -> StrictlyPositiveInt -> StrictlyPositiveInt
minus (Private_ l) (Private_ r) = fromInt (l - r)

-- | Add a StrictlyPositiveInt to another, with the result lower-bounded by one.
plus :: StrictlyPositiveInt -> StrictlyPositiveInt -> StrictlyPositiveInt
plus (Private_ l) (Private_ r) = fromInt (l + r)

one :: StrictlyPositiveInt
one = Private_ 1

--------------------------------------------------------------------------------
-- Instances -------------------------------------------------------------------
--------------------------------------------------------------------------------

instance eqStrictlyPositiveInt :: Eq StrictlyPositiveInt where
    eq (Private_ l) (Private_ r) = l == r

instance ordStrictlyPositiveInt :: Ord StrictlyPositiveInt where
    compare (Private_ l) (Private_ r) = l `compare` r

instance showStrictlyPositiveInt :: Show StrictlyPositiveInt where
    show (Private_ i) = show i

