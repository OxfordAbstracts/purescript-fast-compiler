module TestHoistPureUnit where

import Prelude (class Functor, class Apply, class Applicative, class Bind, class Monad, pure, bind, Unit, unit, map, apply)
import Data.Unit (unit)

-- Bug 3 (datetime-parsing): pure(unit) treated as dict application.
-- The codegen emits pure(Data_Unit.unit) instead of pure(applicativeDict)(Data_Unit.unit).

data MyEither a b = MyLeft a | MyRight b

newtype MyAff a = MyAff a

runMyAff :: forall a. MyAff a -> a
runMyAff (MyAff a) = a

instance functorMyAff :: Functor MyAff where
  map f (MyAff a) = MyAff (f a)

instance applyMyAff :: Apply MyAff where
  apply (MyAff f) (MyAff a) = MyAff (f a)

instance applicativeMyAff :: Applicative MyAff where
  pure a = MyAff a

instance bindMyAff :: Bind MyAff where
  bind (MyAff a) f = f a

instance monadMyAff :: Monad MyAff

-- do-block with case expression containing `pure unit`
check :: MyEither String Int -> MyAff Unit
check result = do
  case result of
    MyLeft _ -> pure unit
    MyRight _ -> pure unit

test :: String
test = case runMyAff (check (MyLeft "err")) of
  _ -> "ok"
-- TEST: "ok"
