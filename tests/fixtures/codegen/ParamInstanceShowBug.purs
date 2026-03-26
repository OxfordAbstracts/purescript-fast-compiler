module ParamInstanceShowBug where
-- TEST: 99

-- Reproduces: Show (f a) constraint resolved as plain Show a.
-- Real bug: shouldContain gets showString for Show (Array String) slot
-- instead of showArray(showString).

class MyClass a where
  extract :: a -> Int

instance myClassInt :: MyClass Int where
  extract x = x

data Box a = Box a

instance myClassBox :: MyClass a => MyClass (Box a) where
  extract (Box x) = extract x

-- Two MyClass constraints: one for `a`, one for `Box a`.
-- Bug: both may resolve to myClassInt, but dictMyClass1 should be myClassBox(myClassInt).
run :: forall a. MyClass a => MyClass (Box a) => Box a -> Int
run x = extract x

test :: Int
test = run (Box 99)
