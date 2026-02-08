module Yoga.Redis where

import Prelude

import Data.Maybe (Maybe)
import Data.Newtype (class Newtype)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Data.Time.Duration (Milliseconds)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, EffectFn4, runEffectFn1, runEffectFn2, runEffectFn3, runEffectFn4)
import Prim.Row (class Union)
import Promise (Promise)
import Promise.Aff (toAffE) as Promise

-- Opaque Redis client type
foreign import data Redis :: Type

-- Newtypes for type safety

-- Connection configuration
newtype RedisHost = RedisHost String
derive instance Newtype RedisHost _
derive newtype instance Eq RedisHost
derive newtype instance Show RedisHost

newtype RedisPort = RedisPort Int
derive instance Newtype RedisPort _
derive newtype instance Eq RedisPort
derive newtype instance Show RedisPort

newtype RedisPassword = RedisPassword String
derive instance Newtype RedisPassword _
derive newtype instance Eq RedisPassword
derive newtype instance Show RedisPassword

newtype RedisDatabase = RedisDatabase Int
derive instance Newtype RedisDatabase _
derive newtype instance Eq RedisDatabase
derive newtype instance Show RedisDatabase

newtype RedisKeyPrefix = RedisKeyPrefix String
derive instance Newtype RedisKeyPrefix _
derive newtype instance Eq RedisKeyPrefix
derive newtype instance Show RedisKeyPrefix

newtype ConnectTimeout = ConnectTimeout Milliseconds
derive instance Newtype ConnectTimeout _
derive newtype instance Eq ConnectTimeout
derive newtype instance Ord ConnectTimeout
derive newtype instance Show ConnectTimeout

newtype KeepAlive = KeepAlive Milliseconds
derive instance Newtype KeepAlive _
derive newtype instance Eq KeepAlive
derive newtype instance Ord KeepAlive
derive newtype instance Show KeepAlive

newtype IPFamily = IPFamily Int
derive instance Newtype IPFamily _
derive newtype instance Eq IPFamily
derive newtype instance Show IPFamily

newtype RetryDelay = RetryDelay Milliseconds
derive instance Newtype RetryDelay _
derive newtype instance Eq RetryDelay
derive newtype instance Ord RetryDelay
derive newtype instance Show RetryDelay

-- Data types
newtype RedisKey = RedisKey String
derive instance Newtype RedisKey _
derive newtype instance Eq RedisKey
derive newtype instance Ord RedisKey
derive newtype instance Show RedisKey

newtype RedisValue = RedisValue String
derive instance Newtype RedisValue _
derive newtype instance Eq RedisValue
derive newtype instance Show RedisValue

newtype RedisField = RedisField String
derive instance Newtype RedisField _
derive newtype instance Eq RedisField
derive newtype instance Ord RedisField
derive newtype instance Show RedisField

newtype RedisChannel = RedisChannel String
derive instance Newtype RedisChannel _
derive newtype instance Eq RedisChannel
derive newtype instance Show RedisChannel

newtype RedisPattern = RedisPattern String
derive instance Newtype RedisPattern _
derive newtype instance Eq RedisPattern
derive newtype instance Show RedisPattern

newtype TTLSeconds = TTLSeconds Int
derive instance Newtype TTLSeconds _
derive newtype instance Eq TTLSeconds
derive newtype instance Ord TTLSeconds
derive newtype instance Show TTLSeconds

newtype TTLMilliseconds = TTLMilliseconds Milliseconds
derive instance Newtype TTLMilliseconds _
derive newtype instance Eq TTLMilliseconds
derive newtype instance Ord TTLMilliseconds
derive newtype instance Show TTLMilliseconds

newtype RedisScore = RedisScore Number
derive instance Newtype RedisScore _
derive newtype instance Eq RedisScore
derive newtype instance Ord RedisScore
derive newtype instance Show RedisScore

-- Create Redis client
type RedisConfigImpl = 
  ( host :: RedisHost
  , port :: RedisPort
  , password :: RedisPassword
  , db :: RedisDatabase
  , keyPrefix :: RedisKeyPrefix
  , connectTimeout :: ConnectTimeout
  , keepAlive :: KeepAlive
  , family :: IPFamily
  , retryStrategy :: Effect (Maybe RetryDelay)
  )

foreign import createRedisImpl :: forall opts. EffectFn1 { | opts } Redis

createRedis :: forall opts opts_. Union opts opts_ RedisConfigImpl => { | opts } -> Effect Redis
createRedis opts = runEffectFn1 createRedisImpl opts

-- Connect
foreign import connectImpl :: EffectFn1 Redis (Promise Unit)

connect :: Redis -> Aff Unit
connect = runEffectFn1 connectImpl >>> Promise.toAffE

-- Disconnect
foreign import disconnectImpl :: EffectFn1 Redis (Promise Unit)

disconnect :: Redis -> Aff Unit
disconnect = runEffectFn1 disconnectImpl >>> Promise.toAffE

-- Quit (graceful disconnect)
foreign import quitImpl :: EffectFn1 Redis (Promise Unit)

quit :: Redis -> Aff Unit
quit = runEffectFn1 quitImpl >>> Promise.toAffE

-- Ping
foreign import pingImpl :: EffectFn1 Redis (Promise String)

ping :: Redis -> Aff String
ping = runEffectFn1 pingImpl >>> Promise.toAffE

-- String Operations

-- Get
foreign import getImpl :: EffectFn2 Redis RedisKey (Promise (Nullable RedisValue))

get :: RedisKey -> Redis -> Aff (Maybe RedisValue)
get key redis = runEffectFn2 getImpl redis key # Promise.toAffE <#> Nullable.toMaybe

-- Set
type SetOptionsImpl = (ex :: TTLSeconds, px :: TTLMilliseconds, nx :: Boolean, xx :: Boolean, keepttl :: Boolean)

foreign import setImpl :: forall opts. EffectFn4 Redis RedisKey RedisValue { | opts } (Promise Unit)

set :: forall opts opts_. Union opts opts_ SetOptionsImpl => RedisKey -> RedisValue -> { | opts } -> Redis -> Aff Unit
set key value opts redis = runEffectFn4 setImpl redis key value opts # Promise.toAffE

-- SetEx (set with expiry in seconds)
foreign import setexImpl :: EffectFn4 Redis RedisKey TTLSeconds RedisValue (Promise Unit)

setex :: RedisKey -> TTLSeconds -> RedisValue -> Redis -> Aff Unit
setex key ttl value redis = runEffectFn4 setexImpl redis key ttl value # Promise.toAffE

-- Del
foreign import delImpl :: EffectFn2 Redis (Array RedisKey) (Promise Int)

del :: Array RedisKey -> Redis -> Aff Int
del keys redis = runEffectFn2 delImpl redis keys # Promise.toAffE

-- Exists
foreign import existsImpl :: EffectFn2 Redis (Array RedisKey) (Promise Int)

exists :: Array RedisKey -> Redis -> Aff Int
exists keys redis = runEffectFn2 existsImpl redis keys # Promise.toAffE

-- Expire
foreign import expireImpl :: EffectFn3 Redis RedisKey TTLSeconds (Promise Boolean)

expire :: RedisKey -> TTLSeconds -> Redis -> Aff Boolean
expire key ttl redis = runEffectFn3 expireImpl redis key ttl # Promise.toAffE

-- TTL
foreign import ttlImpl :: EffectFn2 Redis RedisKey (Promise Int)

ttl :: RedisKey -> Redis -> Aff Int
ttl key redis = runEffectFn2 ttlImpl redis key # Promise.toAffE

-- Increment
foreign import incrImpl :: EffectFn2 Redis RedisKey (Promise Int)

incr :: RedisKey -> Redis -> Aff Int
incr key redis = runEffectFn2 incrImpl redis key # Promise.toAffE

-- IncrBy
foreign import incrByImpl :: EffectFn3 Redis RedisKey Int (Promise Int)

incrBy :: RedisKey -> Int -> Redis -> Aff Int
incrBy key increment redis = runEffectFn3 incrByImpl redis key increment # Promise.toAffE

-- Decrement
foreign import decrImpl :: EffectFn2 Redis RedisKey (Promise Int)

decr :: RedisKey -> Redis -> Aff Int
decr key redis = runEffectFn2 decrImpl redis key # Promise.toAffE

-- DecrBy
foreign import decrByImpl :: EffectFn3 Redis RedisKey Int (Promise Int)

decrBy :: RedisKey -> Int -> Redis -> Aff Int
decrBy key decrement redis = runEffectFn3 decrByImpl redis key decrement # Promise.toAffE

-- Hash Operations

-- HGet
foreign import hgetImpl :: EffectFn3 Redis RedisKey RedisField (Promise (Nullable RedisValue))

hget :: RedisKey -> RedisField -> Redis -> Aff (Maybe RedisValue)
hget key field redis = runEffectFn3 hgetImpl redis key field # Promise.toAffE <#> Nullable.toMaybe

-- HSet
foreign import hsetImpl :: EffectFn3 Redis RedisKey (Array { field :: RedisField, value :: RedisValue }) (Promise Int)

hset :: RedisKey -> Array { field :: RedisField, value :: RedisValue } -> Redis -> Aff Int
hset key fieldValues redis = runEffectFn3 hsetImpl redis key fieldValues # Promise.toAffE

-- HGetAll
foreign import hgetallImpl :: EffectFn2 Redis RedisKey (Promise (Array { field :: RedisField, value :: RedisValue }))

hgetall :: RedisKey -> Redis -> Aff (Array { field :: RedisField, value :: RedisValue })
hgetall key redis = runEffectFn2 hgetallImpl redis key # Promise.toAffE

-- HDel
foreign import hdelImpl :: EffectFn3 Redis RedisKey (Array RedisField) (Promise Int)

hdel :: RedisKey -> Array RedisField -> Redis -> Aff Int
hdel key fields redis = runEffectFn3 hdelImpl redis key fields # Promise.toAffE

-- HExists
foreign import hexistsImpl :: EffectFn3 Redis RedisKey RedisField (Promise Boolean)

hexists :: RedisKey -> RedisField -> Redis -> Aff Boolean
hexists key field redis = runEffectFn3 hexistsImpl redis key field # Promise.toAffE

-- HKeys
foreign import hkeysImpl :: EffectFn2 Redis RedisKey (Promise (Array RedisField))

hkeys :: RedisKey -> Redis -> Aff (Array RedisField)
hkeys key redis = runEffectFn2 hkeysImpl redis key # Promise.toAffE

-- HLen
foreign import hlenImpl :: EffectFn2 Redis RedisKey (Promise Int)

hlen :: RedisKey -> Redis -> Aff Int
hlen key redis = runEffectFn2 hlenImpl redis key # Promise.toAffE

-- List Operations

-- LPush
foreign import lpushImpl :: EffectFn3 Redis RedisKey (Array RedisValue) (Promise Int)

lpush :: RedisKey -> Array RedisValue -> Redis -> Aff Int
lpush key values redis = runEffectFn3 lpushImpl redis key values # Promise.toAffE

-- RPush
foreign import rpushImpl :: EffectFn3 Redis RedisKey (Array RedisValue) (Promise Int)

rpush :: RedisKey -> Array RedisValue -> Redis -> Aff Int
rpush key values redis = runEffectFn3 rpushImpl redis key values # Promise.toAffE

-- LPop
foreign import lpopImpl :: EffectFn2 Redis RedisKey (Promise (Nullable RedisValue))

lpop :: RedisKey -> Redis -> Aff (Maybe RedisValue)
lpop key redis = runEffectFn2 lpopImpl redis key # Promise.toAffE <#> Nullable.toMaybe

-- RPop
foreign import rpopImpl :: EffectFn2 Redis RedisKey (Promise (Nullable RedisValue))

rpop :: RedisKey -> Redis -> Aff (Maybe RedisValue)
rpop key redis = runEffectFn2 rpopImpl redis key # Promise.toAffE <#> Nullable.toMaybe

-- LRange
foreign import lrangeImpl :: EffectFn4 Redis RedisKey Int Int (Promise (Array RedisValue))

lrange :: RedisKey -> Int -> Int -> Redis -> Aff (Array RedisValue)
lrange key start stop redis = runEffectFn4 lrangeImpl redis key start stop # Promise.toAffE

-- LLen
foreign import llenImpl :: EffectFn2 Redis RedisKey (Promise Int)

llen :: RedisKey -> Redis -> Aff Int
llen key redis = runEffectFn2 llenImpl redis key # Promise.toAffE

-- Set Operations

-- SAdd
foreign import saddImpl :: EffectFn3 Redis RedisKey (Array RedisValue) (Promise Int)

sadd :: RedisKey -> Array RedisValue -> Redis -> Aff Int
sadd key members redis = runEffectFn3 saddImpl redis key members # Promise.toAffE

-- SRem
foreign import sremImpl :: EffectFn3 Redis RedisKey (Array RedisValue) (Promise Int)

srem :: RedisKey -> Array RedisValue -> Redis -> Aff Int
srem key members redis = runEffectFn3 sremImpl redis key members # Promise.toAffE

-- SMembers
foreign import smembersImpl :: EffectFn2 Redis RedisKey (Promise (Array RedisValue))

smembers :: RedisKey -> Redis -> Aff (Array RedisValue)
smembers key redis = runEffectFn2 smembersImpl redis key # Promise.toAffE

-- SIsMember
foreign import sismemberImpl :: EffectFn3 Redis RedisKey RedisValue (Promise Boolean)

sismember :: RedisKey -> RedisValue -> Redis -> Aff Boolean
sismember key member redis = runEffectFn3 sismemberImpl redis key member # Promise.toAffE

-- SCard
foreign import scardImpl :: EffectFn2 Redis RedisKey (Promise Int)

scard :: RedisKey -> Redis -> Aff Int
scard key redis = runEffectFn2 scardImpl redis key # Promise.toAffE

-- Sorted Set Operations

-- ZAdd
type ZAddMember = { score :: RedisScore, value :: RedisValue }

type ZAddOptionsImpl = (nx :: Boolean, xx :: Boolean, gt :: Boolean, lt :: Boolean, ch :: Boolean)

foreign import zaddImpl :: forall opts. EffectFn4 Redis RedisKey (Array ZAddMember) { | opts } (Promise Int)

zadd :: forall opts opts_. Union opts opts_ ZAddOptionsImpl => RedisKey -> Array ZAddMember -> { | opts } -> Redis -> Aff Int
zadd key members opts redis = runEffectFn4 zaddImpl redis key members opts # Promise.toAffE

-- ZRem
foreign import zremImpl :: EffectFn3 Redis RedisKey (Array RedisValue) (Promise Int)

zrem :: RedisKey -> Array RedisValue -> Redis -> Aff Int
zrem key members redis = runEffectFn3 zremImpl redis key members # Promise.toAffE

-- ZRange
type ZRangeMember = { value :: RedisValue, score :: RedisScore }

foreign import zrangeImpl :: EffectFn4 Redis RedisKey Int Int (Promise (Array ZRangeMember))

zrange :: RedisKey -> Int -> Int -> Redis -> Aff (Array ZRangeMember)
zrange key start stop redis = runEffectFn4 zrangeImpl redis key start stop # Promise.toAffE

-- ZCard
foreign import zcardImpl :: EffectFn2 Redis RedisKey (Promise Int)

zcard :: RedisKey -> Redis -> Aff Int
zcard key redis = runEffectFn2 zcardImpl redis key # Promise.toAffE

-- ZScore
foreign import zscoreImpl :: EffectFn3 Redis RedisKey RedisValue (Promise (Nullable RedisScore))

zscore :: RedisKey -> RedisValue -> Redis -> Aff (Maybe RedisScore)
zscore key member redis = runEffectFn3 zscoreImpl redis key member # Promise.toAffE <#> Nullable.toMaybe

-- Pub/Sub Operations

-- Publish
foreign import publishImpl :: EffectFn3 Redis RedisChannel RedisValue (Promise Int)

publish :: RedisChannel -> RedisValue -> Redis -> Aff Int
publish channel message redis = runEffectFn3 publishImpl redis channel message # Promise.toAffE
