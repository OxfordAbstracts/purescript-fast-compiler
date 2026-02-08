module FRP.Event.Effect where

import Prelude

import Effect (Effect)
import Effect.Uncurried (mkEffectFn1, runEffectFn1, runEffectFn2)
import FRP.Event (Event, makeEventO, subscribeO)

bindToEffect :: forall a b. Event a -> (a -> Effect b) -> Event b
bindToEffect e f = makeEventO $ mkEffectFn1 \k -> do
  u <- runEffectFn2 subscribeO e $ mkEffectFn1 \v -> do
    o <- f v
    runEffectFn1 k o
  pure u
