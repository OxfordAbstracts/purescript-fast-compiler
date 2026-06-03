module Test.DoLetShadowingNewtype where

-- Reproducer for a suspected do-let shadowing bug in
-- DrStripeRefundAttendee:
--
-- The outer do-block binds `total :: ToAddTotal` (a newtype).
-- A case-branch inner do-block re-binds `total :: Int` via `let
-- total = ...`. This SHOULD shadow the outer `total` for the
-- inner uses. If shadowing leaks, the inner uses see
-- `ToAddTotal` and reject the `Int`-using site as a type
-- mismatch.

newtype ToAddTotal = ToAddTotal Int

useToAddTotal :: ToAddTotal -> Int
useToAddTotal (ToAddTotal n) = n

useInt :: Int -> Int
useInt n = n

data Maybe a = Nothing | Just a

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b
bind Nothing _ = Nothing
bind (Just a) f = f a

pure_ :: forall a. a -> Maybe a
pure_ = Just

-- Replicates the DrStripeRefundAttendee pattern: outer total ::
-- ToAddTotal (passed into `useToAddTotal`), inner re-binds total
-- as Int via case + let.
example :: ToAddTotal -> Int -> Maybe Int
example outerTotal flag =
  bind (pure_ outerTotal) \total ->
    let
      _ = useToAddTotal total  -- here total :: ToAddTotal
    in
      bind (pure_ flag) \_ ->
        let
          total = 42  -- shadows: inner total :: Int
        in
          pure_ (useInt total)  -- should typecheck: total :: Int
