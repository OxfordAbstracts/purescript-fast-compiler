module Test.ComposePoly where

-- Reproduce the compose-direction bug from Next.Router.
-- Three sequential decls all use `event "x" <<< mkEffectFn1`.
-- The first two have monomorphic sigs and pass; the third
-- has a polymorphic forall'd record-tail sig and is the failing
-- pattern in the original bug report.

class Semigroupoid a where
  compose :: forall b c d. a c d -> a b c -> a b d

instance semigroupoidFn :: Semigroupoid (->) where
  compose f g x = f (g x)

infixr 9 compose as <<<

foreign import data Effect :: Type -> Type
foreign import data EffectFn1 :: Type -> Type -> Type

foreign import mkEffectFn1 :: forall a r. (a -> Effect r) -> EffectFn1 a r

data Unit = Unit
data Boolean = TT | FF

foreign import event :: forall a. String -> a -> Effect (Effect Unit)

-- Plain non-polymorphic input — typechecks.
onRouteChangeStart :: (String -> Effect Unit) -> Effect (Effect Unit)
onRouteChangeStart = event "rcs" <<< mkEffectFn1

routeChangeComplete :: (String -> Effect Unit) -> Effect (Effect Unit)
routeChangeComplete = event "rcc" <<< mkEffectFn1

-- Polymorphic record-tail input — this is the failing pattern.
routeChangeError
  :: forall r. ({ cancelled :: Boolean | r } -> Effect Unit) -> Effect (Effect Unit)
routeChangeError = event "rce" <<< mkEffectFn1
