module Level.DB.Resource where
import Control.Promise (Promise)
import Control.Promise as P
import Effect (Effect)
import Effect.Aff (Aff)
import Prelude (Void,Unit,(<$>),($))


data LevelDB :: Type -> Type -> Type
data LevelDB key value = LevelDB LevelJson

open :: forall k v. String -> Effect (LevelDB k v)
open path = LevelDB <$> openJson path

sublevel :: forall k v . LevelDB Void Void -> String -> Effect (LevelDB k v)
sublevel (LevelDB p) path = LevelDB <$> sublevelJson p path

close :: forall k v . LevelDB k v -> Aff Unit
close (LevelDB db) = P.toAffE $ closeJson db


foreign import data LevelJson :: Type

foreign import openJson :: String -> Effect LevelJson

foreign import sublevelJson :: LevelJson -> String -> Effect LevelJson

foreign import closeJson :: LevelJson -> Effect (Promise Unit)


