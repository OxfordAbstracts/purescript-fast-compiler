module Webb.Channel.Data.ReceiveQueue where

import Prelude

import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, modify, unwrap, wrap)
import Webb.Array as Array
import Webb.Channel.Data.Id (Id)
import Webb.Channel.Data.ReceiveItem (RItem)
import Webb.Channel.Data.ReceiveItem as RItem


newtype ReceiveQueue = R (Array RItem)

type RQueue = ReceiveQueue

derive newtype instance Eq ReceiveQueue
derive newtype instance Ord ReceiveQueue
derive newtype instance Show ReceiveQueue
derive instance Newtype ReceiveQueue _

newQueue :: RQueue
newQueue = wrap []

toArray :: RQueue -> Array RItem
toArray queue = unwrap queue

fromArray :: Array RItem -> RQueue
fromArray = wrap

addLast :: RItem -> RQueue -> RQueue
addLast item = modify $ Array.addLast item

first :: RQueue -> Maybe RItem
first = unwrap >>> Array.first

drop :: Int -> RQueue -> RQueue
drop n = modify $ Array.drop n

isEmpty :: RQueue -> Boolean
isEmpty = unwrap >>> Array.isEmpty

size :: RQueue -> Int
size = unwrap >>> Array.size

removeId :: Id -> RQueue -> RQueue
removeId id = modify $ Array.reject (RItem.hasId id)

swap :: Array RItem -> RQueue -> RQueue
swap arr = modify $ const arr