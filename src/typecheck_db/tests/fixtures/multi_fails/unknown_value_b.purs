module Test.MultiFails.UnknownValueB where

-- `missing` isn't in A — expect UnknownValue.
import Test.MultiFails.UnknownValueA (missing)

foo :: Int
foo = 0
