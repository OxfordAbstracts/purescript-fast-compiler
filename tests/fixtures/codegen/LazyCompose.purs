module LazyCompose where
-- TEST: 42

-- Reproduces argonaut-codecs: operator <<< not resolved to compose,
-- and dict args missing for compose and unwrap.

class Semigroupoid a where
  compose :: forall b c d. a c d -> a b c -> a b d

instance semigroupoidFn :: Semigroupoid (->) where
  compose f g x = f (g x)

infixr 9 compose as <<<

class Newtype t a | t -> a where
  unwrap :: t -> a

newtype MyWrapper = MyWrapper Int

instance newtypeMyWrapper :: Newtype MyWrapper Int where
  unwrap (MyWrapper x) = x

addOne :: Int -> Int
addOne x = x

-- Pattern from Data.List.Lazy.Types: step = force <<< unwrap
-- Should be: compose(semigroupoidFn)(addOne)(unwrap(newtypeMyWrapper))
-- Bug: $less$less$less(addOne)(unwrap) — mangled operator, missing dicts
step :: MyWrapper -> Int
step = addOne <<< unwrap

test :: Int
test = step (MyWrapper 42)
