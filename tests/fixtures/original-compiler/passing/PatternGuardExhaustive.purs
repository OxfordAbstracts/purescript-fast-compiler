module PatternGuardExhaustive where

-- Pattern guard with irrefutable record binding should be treated as
-- always-true for exhaustiveness, covering the remaining array cases.
classify :: Array Int -> Int
classify [] = 0
classify [_] = 1
classify [_, _] = 2
classify ns
  | { len } <- { len: 3 } = len
