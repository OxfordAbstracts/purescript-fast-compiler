module Test.Newtype where

-- `newtype` with its single-field constructor used both at
-- value and pattern sites.
newtype Age = Age Int

mkAge :: Int -> Age
mkAge n = Age n

unAge :: Age -> Int
unAge (Age n) = n
