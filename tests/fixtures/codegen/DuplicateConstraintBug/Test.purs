-- MRE for the Data.Map.Internal "Failed pattern match" bug.
--
-- Pattern: instance (Ord k, Ord v) => Ord (Container k v) where
--   compare xs ys = compare (toIter xs) (toIter ys)
--
-- The `compare (toIter xs) (toIter ys)` call needs Ord (Iter k v).
-- The correct dict is: ordIter(dictOrd)(dictOrd1)
-- The buggy dict is:   dictOrd  (just the first Ord constraint, i.e. Ord k)
--
-- TEST: true
module Test where

import Prelude

-- An intermediate iterator type (analogous to MapIter in Data.Map.Internal).
-- Ord (Iter k v) requires both Ord k and Ord v.
data Iter k v = Iter k v

instance eqIter :: (Eq k, Eq v) => Eq (Iter k v) where
  eq (Iter k1 v1) (Iter k2 v2) = eq k1 k2 && eq v1 v2

instance ordIter :: (Ord k, Ord v) => Ord (Iter k v) where
  compare (Iter k1 v1) (Iter k2 v2) =
    let r = compare k1 k2
    in case r of
      EQ -> compare v1 v2
      _ -> r

-- A simple container type.
data Container k v = Container k v

toIter :: forall k v. Container k v -> Iter k v
toIter (Container k v) = Iter k v

instance eqContainer :: (Eq k, Eq v) => Eq (Container k v) where
  eq (Container k1 v1) (Container k2 v2) = eq k1 k2 && eq v1 v2

-- The critical instance: compare via toIter, which needs Ord (Iter k v).
-- Correct codegen: ordIter(dictOrd)(dictOrd1)
-- Buggy codegen:   dictOrd  (Ord k used to compare Iter k v objects)
instance ordContainer :: (Ord k, Ord v) => Ord (Container k v) where
  compare xs ys = compare (toIter xs) (toIter ys)

-- Test: compare (Container 1 "a") (Container 1 "b")
-- toIter gives Iter 1 "a" vs Iter 1 "b"
-- ordIter: compare 1 1 = EQ, then compare "a" "b" = LT  =>  LT  (correct)
-- Bug: ordInt.compare(Iter obj1)(Iter obj2) = GT  (object reference comparison)
-- So compare c1 c2 == LT should be true; with bug it is false.
c1 :: Container Int String
c1 = Container 1 "a"

c2 :: Container Int String
c2 = Container 1 "b"

test :: Boolean
test = compare c1 c2 == LT
