module Test.UnsafePartialCompose where

-- Point-free `unsafePartial <<< case _ of …` composition must
-- discharge the Partial constraint of the non-exhaustive case, the
-- same way the direct `unsafePartial (case …)` form does. The case is
-- the argument of `<<<`, not of `unsafePartial`, so the discharge has
-- to recognise that `unsafePartial` sits in the function position of
-- the surrounding application chain.
data Maybe a = Nothing | Just a

foreign import unsafePartial :: forall a. (Partial => a) -> a

-- Concrete-arrow `compose` so the test needs no Semigroupoid class;
-- this preserves the `App(App(<<<, unsafePartial), caseLambda)` shape
-- the real Prelude `<<<` produces.
foreign import compose :: forall b c d. (c -> d) -> (b -> c) -> (b -> d)

infixr 9 compose as <<<

-- `case _ of` section desugars to a lambda; composed with
-- unsafePartial via `<<<`.
fromJust :: forall a. Maybe a -> a
fromJust = unsafePartial <<< case _ of
  Just x -> x
