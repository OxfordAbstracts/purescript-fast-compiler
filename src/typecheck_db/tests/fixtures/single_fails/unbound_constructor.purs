module Test.UnboundCtor where

-- Constructor `Zebra` isn't declared anywhere — expect
-- UnboundConstructor.
foo :: Int
foo = case 0 of
  Zebra -> 1
  _ -> 0
