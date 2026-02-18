-- Regression test: data types with higher-rank constructor fields containing
-- forall-bound type variables whose kinds depend on the outer data type's
-- type parameters should not trigger "Cannot unambiguously generalize kinds".
--
-- The inner forall's type variables (slot, m) have kinds that are determined
-- by unification with the outer parameters (g, f). The kind checker must
-- exclude the outer type parameter kind variables when checking the inner
-- forall's quantification.
module NestedForallKindGeneralization where

import Prelude

data Wrapper g f a =
  Wrapper
    (forall slot m. Applicative m => (slot g -> m a) -> m (f a))
    (g a)
    (f a -> a)
