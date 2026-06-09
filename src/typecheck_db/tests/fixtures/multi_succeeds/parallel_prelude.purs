module Test.Multi.ParallelPrelude where

-- Self-contained Prelude-ish module for the RouteToPage repro.
-- The `ado` desugar emits unqualified `map` and `apply` calls (per
-- desugar/do_notation.rs::desugar_ado), so these names must resolve
-- to the standard class methods.

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

infixl 4 map as <$>

mapFlipped :: forall f a b. Functor f => f a -> (a -> b) -> f b
mapFlipped fa f = map f fa

infixl 1 mapFlipped as <#>

class Functor f <= Apply f where
  apply :: forall a b. f (a -> b) -> f a -> f b

infixl 4 apply as <*>

applyFlipped :: forall a b. a -> (a -> b) -> b
applyFlipped a f = f a

infixl 1 applyFlipped as #

dollar :: forall a b. (a -> b) -> a -> b
dollar f a = f a

infixr 0 dollar as $

class Parallel f g | f -> g, g -> f where
  parallel :: forall a. g a -> f a
  sequential :: forall a. f a -> g a

data Aff a = Aff
data ParAff a = ParAff

instance Functor Aff where
  map _ _ = Aff

instance Apply Aff where
  apply _ _ = Aff

instance Functor ParAff where
  map _ _ = ParAff

instance Apply ParAff where
  apply _ _ = ParAff

instance Parallel ParAff Aff where
  parallel _ = ParAff
  sequential _ = Aff
