module Test.Records where

-- Closed record literal.
point :: { x :: Int, y :: Int }
point = { x: 1, y: 2 }

-- Open-row access: `r.x` works for any record with an `x` field.
getX :: forall r. { x :: Int | r } -> Int
getX r = r.x

-- Record update preserves the record shape.
bumpX :: forall r. { x :: Int | r } -> { x :: Int | r }
bumpX r = r { x = 7 }

-- Record-literal pun: `{ x }` means `{ x: x }`.
wrap :: Int -> { x :: Int }
wrap x = { x }
