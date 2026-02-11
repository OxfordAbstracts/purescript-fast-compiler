module ApplicativePhases.Day where

import Prelude

import Data.Tuple (Tuple(..))

newtype Day f g a = Day (∀ r. (∀ y z. (y → z → a) → f y → g z → r) → r)

instance Functor (Day f g) where
  map f (Day unwrap) = unwrap \c → mkDay (\y z → f (c y z))

instance (Apply f, Apply g) ⇒ Apply (Day f g) where
  apply (Day unwrapF) (Day unwrapA) =
    unwrapF \c1 fxs gxs → unwrapA \c2 fys gys → mkDay
      (\(Tuple fx fy) (Tuple gx gy) → (c1 fx gx) (c2 fy gy))
      (Tuple <$> fxs <*> fys)
      (Tuple <$> gxs <*> gys)

instance (Applicative f, Applicative g) ⇒ Applicative (Day f g) where
  pure x = mkDay (\_ _ → x) (pure unit) (pure unit)

mkDay ∷ ∀ @f @g @a @x @y. (x → y → a) → f x → g y → Day f g a
mkDay c f g = Day \res → res c f g

unwrapDay ∷ ∀ @f @g @a @r. (∀ x y. (x → y → a) → f x → g y → r) → Day f g a → r
unwrapDay res (Day day) = day res

runDay ∷ ∀ @f. Applicative f ⇒ Day f f ~> f
runDay = unwrapDay \c f g → c <$> f <*> g

phaseA ∷ ∀ @f @g. Applicative g ⇒ f ~> Day f g
phaseA f = mkDay (\x _ → x) f (pure unit)

phaseB ∷ ∀ @f @g. Applicative f ⇒ g ~> Day f g
phaseB g = mkDay (\_ x → x) (pure unit) g

hoistA ∷ ∀ @f @f' @g. (f ~> f') → (Day f g ~> Day f' g)
hoistA nat = unwrapDay \c f g → mkDay c (nat f) g

hoistB ∷ ∀ @g @g' @f. (g ~> g') → (Day f g ~> Day f g')
hoistB nat = unwrapDay \c f g → mkDay c f (nat g)
