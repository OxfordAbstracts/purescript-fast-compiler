module Test.ParallelAdoFundep where

-- Minimal repro of the AdminDashboard.RouteToPage failure pattern:
--   sequential ado
--     page <- parallel $ model # init <#> Wrap
--     in page
--
-- where `init :: a -> Aff PageModel`, `PageModel` is a record, and
-- `Wrap :: PageModel -> Page`.
--
-- The expected behaviour: parallel's `f` gets unified with `?f Page`,
-- and the fundep `g -> f` on `Parallel f g` (with g = Aff) discharges
-- the constraint via the `Parallel ParAff Aff` instance.

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

mapFlipped :: forall f a b. Functor f => f a -> (a -> b) -> f b
mapFlipped fa f = map f fa

infixl 1 mapFlipped as <#>

applyFlipped :: forall a b. a -> (a -> b) -> b
applyFlipped a f = f a

infixl 1 applyFlipped as #

apply :: forall a b. (a -> b) -> a -> b
apply f a = f a

infixr 0 apply as $

class Parallel f g | f -> g, g -> f where
  parallel :: forall a. g a -> f a
  sequential :: forall a. f a -> g a

data Aff a = Aff
data ParAff a = ParAff

instance Functor Aff where
  map _ _ = Aff

instance Functor ParAff where
  map _ _ = ParAff

instance Parallel ParAff Aff where
  parallel _ = ParAff
  sequential _ = Aff

type PageModel = { x :: Int, y :: Int }

init :: forall a. a -> Aff PageModel
init _ = Aff

data Page = Wrap PageModel

test :: forall a. a -> Aff Page
test model = sequential ado
  page <- parallel $ model # init <#> Wrap
  in page
