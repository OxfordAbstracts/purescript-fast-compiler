module Test.UnboundVar where

-- `missingThing` is nowhere in scope — expect UnboundVar.
foo :: Int
foo = missingThing
