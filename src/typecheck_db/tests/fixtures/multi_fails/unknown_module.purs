module Test.MultiFails.UnknownModule where

-- Importing a module that isn't in the registry (and isn't a
-- Prim submodule) must produce `UnknownModule`.
import Test.DoesNotExist

foo :: Int
foo = 0
