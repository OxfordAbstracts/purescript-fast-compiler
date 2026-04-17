module Test.WrongType where

-- `Wrap` has type `Int -> Wrap`. Applying it to a String must
-- fail unification. This path doesn't rely on signature-guided
-- inference (a gap the checker still has), just on constructor
-- argument matching.
data Wrap = Wrap Int

bad :: Wrap
bad = Wrap "not an int"
