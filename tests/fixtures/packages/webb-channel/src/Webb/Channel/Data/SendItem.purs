module Webb.Channel.Data.SendItem where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Unsafe.Coerce (unsafeCoerce)
import Webb.Channel.Data.Id (Id)
import Webb.Result (Result)



newtype SendItem = S 
  { result :: Result Boolean -- To notify the sender, if it is waiting.
  , value :: Void -- The value to be delivered.
  , show :: Maybe String -- We may want to show the items for debugging.
  , id :: Id
  }
  
type SItem = SendItem
  
instance Eq SendItem where
  eq (S a) (S b) = a.id == b.id
instance Ord SendItem where
  compare (S a) (S b) = compare a.id b.id
derive instance Newtype SendItem _
instance Show SendItem where 
  show (S i) = show { id: i.id, show: i.show }

newItem :: forall a. Show a => a -> Id -> Result Boolean -> SendItem
newItem a id' result' = wrap 
  { result: result'
  , value: voided a
  , show: Just (show a ) 
  , id: id'
  }

newItem' :: forall a. a -> Id -> Result Boolean -> SendItem
newItem' a id' result' = wrap 
  { result: result'
  , value: voided a
  , show: Nothing
  , id: id'
  }

voided :: forall a. a -> Void
voided = unsafeCoerce

unvoided :: forall a. Void -> a
unvoided = unsafeCoerce
  
result :: SendItem -> Result Boolean
result = unwrap >>> _.result

value :: SendItem -> Void
value = unwrap >>> _.value

id :: SendItem -> Id
id = unwrap >>> _.id

hasId :: Id -> SendItem -> Boolean
hasId id' item = id item == id'