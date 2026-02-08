module Yoga.Redis.PubSub where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Prim.Row (class Union)
import Promise (Promise)
import Promise.Aff (toAffE) as Promise
import Yoga.Redis (ConnectTimeout, IPFamily, KeepAlive, Redis, RedisChannel, RedisDatabase, RedisHost, RedisKeyPrefix, RedisPassword, RedisPattern, RedisPort, RedisValue)

-- Opaque subscriber type (separate from main Redis client for pub/sub)
foreign import data RedisSubscriber :: Type

-- Subscription message payload
type SubscriptionMessage =
  { channel :: RedisChannel
  , message :: RedisValue
  }

-- Pattern subscription message payload
type PatternMessage =
  { pattern :: RedisPattern
  , channel :: RedisChannel
  , message :: RedisValue
  }

-- Create subscriber (separate client for subscriptions)
type RedisSubscriberConfigImpl =
  ( host :: RedisHost
  , port :: RedisPort
  , password :: RedisPassword
  , db :: RedisDatabase
  , keyPrefix :: RedisKeyPrefix
  , connectTimeout :: ConnectTimeout
  , keepAlive :: KeepAlive
  , family :: IPFamily
  )

foreign import createSubscriberImpl :: forall opts. EffectFn1 { | opts } RedisSubscriber

createSubscriber :: forall opts opts_. Union opts opts_ RedisSubscriberConfigImpl => { | opts } -> Effect RedisSubscriber
createSubscriber = runEffectFn1 createSubscriberImpl

-- Subscribe to channels
foreign import subscribeImpl :: EffectFn3 RedisSubscriber (Array RedisChannel) (SubscriptionMessage -> Effect Unit) (Promise Unit)

subscribe :: Array RedisChannel -> (SubscriptionMessage -> Effect Unit) -> RedisSubscriber -> Aff Unit
subscribe channels handler subscriber =
  runEffectFn3 subscribeImpl subscriber channels handler # Promise.toAffE

-- Unsubscribe from channels
foreign import unsubscribeImpl :: EffectFn2 RedisSubscriber (Array RedisChannel) (Promise Unit)

unsubscribe :: Array RedisChannel -> RedisSubscriber -> Aff Unit
unsubscribe channels subscriber = runEffectFn2 unsubscribeImpl subscriber channels # Promise.toAffE

-- Pattern subscribe
foreign import psubscribeImpl :: EffectFn3 RedisSubscriber (Array RedisPattern) (PatternMessage -> Effect Unit) (Promise Unit)

psubscribe :: Array RedisPattern -> (PatternMessage -> Effect Unit) -> RedisSubscriber -> Aff Unit
psubscribe patterns handler subscriber =
  runEffectFn3 psubscribeImpl subscriber patterns handler # Promise.toAffE

-- Pattern unsubscribe
foreign import punsubscribeImpl :: EffectFn2 RedisSubscriber (Array RedisPattern) (Promise Unit)

punsubscribe :: Array RedisPattern -> RedisSubscriber -> Aff Unit
punsubscribe patterns subscriber = runEffectFn2 punsubscribeImpl subscriber patterns # Promise.toAffE

-- Disconnect subscriber
foreign import disconnectSubscriberImpl :: EffectFn1 RedisSubscriber (Promise Unit)

disconnectSubscriber :: RedisSubscriber -> Aff Unit
disconnectSubscriber = runEffectFn1 disconnectSubscriberImpl >>> Promise.toAffE

-- Quit subscriber (graceful disconnect)
foreign import quitSubscriberImpl :: EffectFn1 RedisSubscriber (Promise Unit)

quitSubscriber :: RedisSubscriber -> Aff Unit
quitSubscriber = runEffectFn1 quitSubscriberImpl >>> Promise.toAffE
