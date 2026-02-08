module Level.DB.Iterator.Options where
import Data.Argonaut (class EncodeJson, encodeJson)
import Data.Array (elem)
import Data.Options (Option, Options(..), opt)
import Data.Tuple (Tuple(..))
import Unsafe.Coerce (unsafeCoerce)
import Prelude ((<$>))

data IteratorOptions :: Type -> Type
data IteratorOptions k

jsonify :: forall k . EncodeJson k => Options (IteratorOptions k) -> Options (IteratorOptions k)
jsonify (Options o) = Options (go <$> o)
  where
    go (Tuple op k) | op `elem` ["gt","gte","lt","lte"]
                    = Tuple op (unsafeCoerce (encodeJson (unsafeCoerce k :: k))) 
    go t = t

gt :: forall k . Option (IteratorOptions k) k 
gt = opt "gt"

gte :: forall k . Option (IteratorOptions k) k 
gte = opt "gte"

lt :: forall k . Option (IteratorOptions k) k 
lt = opt "lt"

lte :: forall k . Option (IteratorOptions k) k 
lte = opt "lte"

reverse :: forall k . Option (IteratorOptions k) Boolean
reverse = opt "reverse"

limit :: forall k . Option (IteratorOptions k) Int
limit = opt "limit"


