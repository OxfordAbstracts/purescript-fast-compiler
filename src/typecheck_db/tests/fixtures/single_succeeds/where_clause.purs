module Test.WhereClause where

-- `where`-clause brings `helper` into scope for the body.
-- Driver lowers the clause into a synthetic `let` around the
-- body expression.
hundred :: Int
hundred = helper 10
  where
    helper n = n

-- Multi-equation + where: each clause's body can use the
-- where-bound name.
label :: Int -> String
label 0 = prefix
  where
    prefix = "zero"
label _ = "other"
