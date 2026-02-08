module FixFunctor where

import Prelude

class HFunctor ∷ ∀ k1 k2. ((k1 → Type) → k2 → Type) → Constraint
class HFunctor f where
  hmap ∷ ∀ a b. (a ~> b) → f a ~> f b

newtype Fix ∷ ∀ k. ((k → Type) → k → Type) → k → Type
newtype Fix f a = Fix (f (Fix f) a)

cata ∷ ∀ @g @f. HFunctor f ⇒ (f g ~> g) → (Fix f ~> g)
cata nat (Fix f) = nat (hmap (cata nat) f)
