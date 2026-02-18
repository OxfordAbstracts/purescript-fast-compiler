module Rank2MultiEquation where

-- Tests that multi-equation functions with rank-2 parameter types correctly
-- propagate the signature to each equation. Without this, the rank-2
-- parameter `f` gets a bare unification variable, and passing it to a
-- recursive call triggers a false "type variable has escaped its scope" error.

data Tree a = Leaf a | Branch (Tree a) (Tree a)

mapTree :: forall a b. (forall x. x -> x) -> Tree a -> Tree a
mapTree _ (Leaf x) = Leaf x
mapTree f (Branch l r) = Branch (mapTree f l) (mapTree f r)
