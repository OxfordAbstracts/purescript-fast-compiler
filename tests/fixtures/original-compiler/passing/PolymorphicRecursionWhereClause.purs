module PolymorphicRecursionWhereClause where

-- When a polymorphic function is called recursively from a where-clause
-- with a monomorphic specialization, the self-recursive type must use
-- a polymorphic scheme rather than a bare unification variable.

data Free f a = Pure a | Bind (f (Free f a))
data TestF a = TestA String a | TestB (Free TestF Int) a

hasOnly :: forall a. Free TestF a -> Boolean
hasOnly = go
  where
    go :: forall b. Free TestF b -> Boolean
    go (Pure _) = true
    go (Bind (TestA _ rest)) = go rest
    go (Bind (TestB inner rest)) = if hasOnly inner then go rest else false
