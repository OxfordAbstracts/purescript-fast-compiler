-- Capability-discharge pattern: a nullary class `Cap` with no
-- instances is provided structurally by `withCap`, whose argument is
-- a rank-2 constrained value `(Cap => a)`. Passing a constrained
-- value to `withCap` must discharge `Cap` against the argument's own
-- constraint, NOT surface a spurious `NoInstanceFound Cap`.
-- Mirrors OaVirtual.Capability.Resource.Gql.PublicEvent.AuthComponent.
module Test where

class Cap

foreign import data Component :: Type

withCap :: forall a. (Cap => a) -> a
withCap = withCap_

foreign import withCap_ :: forall a b. a -> b

wrap :: (Cap => Component) -> Component
wrap inner = withCap inner
