module Level.DB.Iterator where
import Level.DB.Resource (LevelDB(..), LevelJson)
import Level.DB.Iterator.Options
import Level.DB.Undefined (Undefined, fromUndefined)
import Level.DB.Mapping (decodeMapping)
import Control.Monad.Rec.Class (class MonadRec, tailRecM, Step(..))
import Control.Monad.Resource (acquire)
import Control.Monad.Resource.Class (class MonadResource)
import Control.Monad.Trans.Class (lift)
import Control.Promise (Promise)
import Control.Promise as P
import Data.Argonaut (class EncodeJson, class DecodeJson, Json)
import Data.Either (Either(..))
import Data.Maybe (Maybe, maybe)
import Data.Options (Options,options)
import Data.Traversable (traverse)
import Data.Tuple (Tuple,snd)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (error,throwException)
import Foreign (Foreign)
import Pipes (yield)
import Pipes.Core (Producer)
import Prelude (Unit,bind,pure,show,unit,($),(<$>),(>>=),(*>))

data Iterator :: Type -> Type -> Type
data Iterator k v = Iterator IteratorJson

iterator :: forall k v . EncodeJson k => LevelDB k v -> Options (IteratorOptions k) -> Effect (Iterator k v)
iterator (LevelDB db) opts = Iterator <$> iteratorJson db (options (jsonify opts))

producer :: forall k v m . 
            MonadResource m
         => MonadRec m
         => EncodeJson k
         => DecodeJson k
         => DecodeJson v
         => LevelDB k v -> Options (IteratorOptions k) -> Producer (Tuple k v) m Unit
producer db opts = do
  it <- lift (snd <$> acquire openIterator closeIterator) 
  tailRecM (produce it) unit
  where
    openIterator :: Aff (Iterator k v)
    openIterator = liftEffect $ iterator db opts
    produce :: Iterator k v -> Unit -> Producer (Tuple k v) m (Step Unit Unit)
    produce it _ = liftAff (next it) >>= maybe (pure (Done unit)) (\t -> yield t *> pure (Loop unit))

next :: forall k v . DecodeJson k => DecodeJson v => Iterator k v -> Aff (Maybe (Tuple k v))
next (Iterator it) = do
  res <- P.toAffE $ nextJson it
  traverse decode (fromUndefined res)
  where
    decode kv = case decodeMapping kv of
                  Left err -> liftEffect $ throwException $ error $ show err
                  Right tup -> pure tup

closeIterator :: forall k v . Iterator k v -> Aff Unit
closeIterator (Iterator it) = P.toAffE $ closeIteratorImpl it

foreign import data IteratorJson :: Type

foreign import iteratorJson :: LevelJson -> Foreign -> Effect IteratorJson

foreign import nextJson :: IteratorJson -> Effect (Promise (Undefined Json))

foreign import closeIteratorImpl :: IteratorJson -> Effect (Promise Unit)

