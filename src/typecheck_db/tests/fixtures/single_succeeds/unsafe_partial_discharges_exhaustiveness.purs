module Test.UnsafePartialDischarge where

-- `unsafePartial :: (Partial => a) -> a` discharges the Partial
-- constraint of its argument, so a non-exhaustive case wrapped in it
-- must NOT produce an exhaustiveness diagnostic.
data Maybe a = Nothing | Just a

foreign import unsafePartial :: forall a. (Partial => a) -> a

-- Direct application form: `unsafePartial (case ...)`.
fromJust :: forall a. Maybe a -> a
fromJust m =
  unsafePartial
    ( case m of
        Just x -> x
    )

-- Lambda-bodied form: the non-exhaustive case sits inside a lambda
-- that is the argument to unsafePartial.
fromJustFn :: forall a. Maybe a -> a
fromJustFn =
  unsafePartial
    ( \m -> case m of
        Just x -> x
    )
