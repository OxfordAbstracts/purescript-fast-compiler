module Level.DB.Operations where

import Level.DB.Resource (LevelDB(..), LevelJson)
import Level.DB.Undefined (Undefined, isUndefined)
import Level.DB.Mapping (decodeMapping)
import Control.Promise (Promise)
import Control.Promise as P
import Data.Argonaut (class DecodeJson, class EncodeJson, Json, decodeJson, encodeJson)
import Data.Array (head)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (error,throwException)
import Prelude
import Unsafe.Coerce (unsafeCoerce)


get :: forall k v . EncodeJson k => DecodeJson k => EncodeJson v => DecodeJson v
    => LevelDB k v -> k -> Aff (Maybe v)
get (LevelDB db) k = do
  res <- P.toAffE $ getJson db (encodeJson k)
  if isUndefined res
    then pure Nothing
    else case decodeJson $ unsafeCoerce res of
           Left err -> liftEffect $ throwException $ error $ show err
           Right obj -> pure $ Just obj

put :: forall k v . EncodeJson k => DecodeJson k => EncodeJson v => DecodeJson v => LevelDB k v -> k -> v -> Aff Unit
put (LevelDB db) k v = P.toAffE $ putJson db (encodeJson k) (encodeJson v)

del :: forall k v . EncodeJson k => DecodeJson k => EncodeJson v => DecodeJson v => LevelDB k v -> k -> Aff Unit
del (LevelDB db) k = P.toAffE $ delJson db (encodeJson k)

all :: forall k v . DecodeJson k => DecodeJson v => LevelDB k v -> Aff (Array (Tuple k v)) 
all (LevelDB db) = do
  res <- P.toAffE $ allJson db
  case traverse decodeMapping res of
    Left err -> liftEffect $ throwException $ error $ show err
    Right arr -> pure arr

nextEntryUp :: forall k v .
               EncodeJson k
            => DecodeJson k
            => DecodeJson v
            => LevelDB k v -> k -> Aff (Maybe (Tuple k v)) 
nextEntryUp (LevelDB db) key = do
  res <- P.toAffE $ nextEntryUpJson db (encodeJson key)
  case traverse decodeMapping res of
    Left err -> liftEffect $ throwException $ error $ show err
    Right arr -> pure $ head arr

nextEntryDn :: forall k v .
               EncodeJson k
            => DecodeJson k
            => DecodeJson v
            => LevelDB k v -> k -> Aff (Maybe (Tuple k v)) 
nextEntryDn (LevelDB db) key = do
  res <- P.toAffE $ nextEntryDnJson db (encodeJson key)
  case traverse decodeMapping res of
    Left err -> liftEffect $ throwException $ error $ show err
    Right arr -> pure $ head arr


allKeys :: forall k v . DecodeJson k => DecodeJson v => LevelDB k v -> Aff (Array k) 
allKeys (LevelDB db) = do
  res <- P.toAffE $ allKeysJson db
  case traverse decodeJson res of
    Left err -> liftEffect $ throwException $ error $ show err
    Right arr -> pure arr

getMany :: forall k v . EncodeJson k => DecodeJson v
        => LevelDB k v -> Array k -> Aff (Array (Maybe v))
getMany (LevelDB db) keys = do
  res <- P.toAffE $ getManyJson db (encodeJson <$> keys)
  liftEffect $ traverse decodeDefined res 
  where
    decodeDefined :: Undefined Json -> Effect (Maybe v)
    decodeDefined val =
      if isUndefined val
        then pure Nothing
        else case decodeJson $ unsafeCoerce val of
               Left err -> throwException $ error $ show err
               Right va -> pure $ Just va

putMany :: forall k v . EncodeJson k => EncodeJson v => LevelDB k v -> Array (Tuple k v) -> Aff Unit
putMany (LevelDB db) ops = P.toAffE $ batchJson db (toOp <$> ops) 
  where
    toOp :: Tuple k v -> Json
    toOp (Tuple k v) = encodeJson { "type": "put", key: encodeJson k, value: encodeJson v }


delMany :: forall k v . EncodeJson k => EncodeJson v => LevelDB k v -> Array k -> Aff Unit
delMany (LevelDB db) ops = P.toAffE $ batchJson db (toOp <$> ops) 
  where
    toOp :: k -> Json
    toOp k = encodeJson { "type": "del", key: encodeJson k }


onPut :: forall k v . DecodeJson k => DecodeJson v 
      => LevelDB k v -> (k -> v -> Effect Unit) -> Effect Unit
onPut (LevelDB db) f = onPutJson db g
  where g :: Json -> Json -> Effect Unit
        g k v = do
          case decodeJson k of
            Left err -> throwException $ error $ show err
            Right kd ->
              case decodeJson v of
                Left err -> throwException $ error $ show err
                Right vd -> f kd vd

foreign import getJson :: LevelJson -> Json -> Effect (Promise (Undefined Json))

foreign import batchJson :: LevelJson -> Array Json -> Effect (Promise Unit)

foreign import getManyJson :: LevelJson -> Array Json -> Effect (Promise (Array (Undefined Json)))

foreign import putJson :: LevelJson -> Json -> Json -> Effect (Promise Unit) 

foreign import delJson :: LevelJson -> Json -> Effect (Promise Unit)

foreign import allJson :: LevelJson -> Effect (Promise (Array Json))

foreign import allKeysJson :: LevelJson -> Effect (Promise (Array Json))

foreign import nextEntryUpJson :: LevelJson -> Json -> Effect (Promise (Array Json))

foreign import nextEntryDnJson :: LevelJson -> Json -> Effect (Promise (Array Json))

foreign import onPutJson :: LevelJson -> (Json -> Json -> Effect Unit) -> Effect Unit


