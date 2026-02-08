module Webb.Stateful where

import Prelude
import Webb.State.Prelude

import Effect (Effect)
import Effect.Unsafe (unsafePerformEffect)


localEffect :: forall a. Effect a -> a
localEffect prog = unsafePerformEffect prog

defaultEq :: forall r s. Eq s => Refer s r => r -> r -> Boolean
defaultEq a b = localEffect do
  a' <- aread a
  b' <- aread b
  pure $ a' == b'

defaultCompare :: forall r s. Ord s => Refer s r => r -> r -> Ordering
defaultCompare a b = localEffect do
  a' <- aread a
  b' <- aread b
  pure $ compare a' b'