module Test.DoCaseDoLetShadowing where

-- Closer mirror of the DrStripeRefundAttendee pattern that the
-- earlier `do_let_shadowing_newtype` fixture didn't catch:
--
--   do                          -- outer Aff-ish do
--     let total = ToAddTotal x  -- outer total :: ToAddTotal
--     ...
--     case plan of
--       Right x -> do            -- inner do
--         let total = sum xs    -- inner total :: Int (shadows outer)
--         useRec { total }      -- pun in record literal — must see Int
--       Left _ -> pure unit
--
-- The pun shape is what the real DrStripeRefundAttendee uses:
-- `{ setup, total, subtotal, plan: success }`. If shadowing leaks
-- across `case` arm + nested do, the inner `total` pun resolves to
-- the outer's `ToAddTotal` and `useRec` errors with Mismatch(Int,
-- ToAddTotal).

newtype ToAddTotal = ToAddTotal Int

useToAddTotal :: ToAddTotal -> Int
useToAddTotal (ToAddTotal n) = n

useRec :: { total :: Int, subtotal :: Int } -> Int
useRec { total } = total

data Maybe a = Nothing | Just a

class Bind m where
  bind :: forall a b. m a -> (a -> m b) -> m b

class Bind m <= Pure m where
  pure :: forall a. a -> m a

data Eff a = EffNop

instance Bind Eff where
  bind _ _ = EffNop

instance Pure Eff where
  pure _ = EffNop

infixl 1 bind as >>=

data Plan = Success Int | Failure

getOuterTotal :: Int -> { total :: ToAddTotal, subtotal :: Int }
getOuterTotal n = { total: ToAddTotal n, subtotal: n }

example :: Int -> Plan -> Eff Int
example seed plan = do
  -- Record-destructure let with FIELD RENAMING — mirrors
  -- DrStripeRefundAttendee's
  --   `let { total, subtotal: toAddSubtotal, ... } = ...`.
  let { total, subtotal: toAddSubtotal } = getOuterTotal seed
  let _ = useToAddTotal total     -- outer total :: ToAddTotal
  case plan of
    Success xs -> do
      let
        total = xs                -- inner total :: Int (shadows)
        subtotal = toAddSubtotal  -- inner subtotal :: Int (Int + Int = Int)
      pure (useRec { total, subtotal })  -- pun: must resolve to inner
    Failure -> pure 0
