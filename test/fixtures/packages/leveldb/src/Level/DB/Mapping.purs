module Level.DB.Mapping where
import Data.Argonaut (class DecodeJson, decodeJson, Json, toArray)
import Data.Argonaut.Decode.Error (JsonDecodeError(..))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Prelude (bind,pure,($))

decodeMapping :: forall k v .
                 DecodeJson k
              => DecodeJson v
              => Json -> Either JsonDecodeError (Tuple k v)
decodeMapping j =
  case toArray j of
    Just [dk,dv] -> do 
      k <- decodeJson dk
      v <- decodeJson dv
      pure $ Tuple k v 
    _ -> Left (UnexpectedValue j)

