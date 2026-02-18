module RecordRowTypeAlias where

-- Tests that App(Con("Record"), row) correctly unifies with Record(fields, tail)
-- by converting to structural record form before unification.

class Merge (r1 :: Row Type) (r2 :: Row Type) (r3 :: Row Type) | r1 r2 -> r3

merge :: forall r1 r2 r3. Merge r1 r2 r3 => Record r1 -> Record r2 -> Record r3
merge _ _ = unsafeCoerce 0

identity' :: forall r. Record r -> Record r
identity' x = x

test :: forall r1 r2 r3. Merge r1 r2 r3 => Record r1 -> Record r2 -> Record r3
test a b = identity' (merge a b)

foreign import unsafeCoerce :: forall a b. a -> b
