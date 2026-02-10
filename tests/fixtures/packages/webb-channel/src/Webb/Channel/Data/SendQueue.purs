module Webb.Channel.Data.SendQueue where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Lens (Lens', over, set)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, modify, unwrap, wrap)
import Data.Show.Generic (genericShow)
import Type.Proxy (Proxy(..))
import Webb.Array as Array
import Webb.Channel.Data.Id (Id)
import Webb.Channel.Data.SendItem (SendItem, SItem)
import Webb.Channel.Data.SendItem as SItem
import Webb.State.Prelude (views)

{- The send queue. This will queue waiting senders, and senders who
  _aren't_ waiting. The decision on whether to wait is left up to the
  sender, by using the SendItem's "Result" object.
-}

newtype SendQueue = B
  { array :: Array SendItem
  , size :: SendSize
  }
  
type SQueue = SendQueue

_array :: forall a r. Lens' { array :: a | r } a
_array = prop (Proxy :: Proxy "array")

_size :: forall a r. Lens' { size :: a | r } a
_size = prop (Proxy :: Proxy "size")
  
derive instance Eq (SendQueue)
derive instance Ord (SendQueue)
derive newtype instance Show (SendQueue)
derive instance Newtype (SendQueue) _
  
data SendSize = Finite Int | Infinite
derive instance Eq SendSize
derive instance Ord SendSize
derive instance Generic SendSize _
instance Show SendSize where show = genericShow

newQueue :: SendSize -> SendQueue 
newQueue size' = fromArray (actual size') []

toArray :: SendQueue -> Array SItem
toArray = unwrap >>> _.array

fromArray :: SendSize -> Array SItem -> SendQueue 
fromArray size' arr = wrap { array: arr, size: (actual size') }

actual :: SendSize -> SendSize
actual = case _ of
  Infinite -> Infinite
  Finite n -> Finite (max 0 n)

-- Before we add, we have to check if the buffer is full according
-- to its size.
isFull :: SendQueue -> Boolean
isFull (B s) = case s.size of
  Infinite -> false
  Finite n -> Array.size s.array >= n
  
isEmpty :: SendQueue -> Boolean
isEmpty = unwrap >>> views _array (Array.isEmpty)
  
size :: SendQueue -> Int
size = unwrap >>> views _array (Array.size)
  
addLast :: SendItem -> SendQueue -> SendQueue 
addLast a = modify $ over _array (Array.addLast a)

first :: SendQueue -> Maybe SItem
first = unwrap >>> views _array (Array.first)

drop :: Int -> SendQueue -> SendQueue 
drop n = modify $ over _array (Array.drop n)

buffer :: SendQueue -> Array SItem
buffer q = toArray $ removePending q

-- Remove the id if it no longer needs to be in the queue, because the
-- one waiting for it has been _cancelled_.
removeId :: Id -> SendQueue -> SendQueue
removeId id = modify $ over _array (Array.reject (SItem.hasId id))

-- These are the pending send items that aren't yet in the buffer
pending :: SendQueue -> Array SendItem
pending (B s) = case s.size of
  Infinite -> []
  Finite n -> Array.drop n s.array
  
-- Get rid of the pending items.
removePending :: SendQueue -> SendQueue
removePending this@(B s) = let 
  count = Array.size $ pending this
  in wrap $ over _array (Array.dropEnd count) s
  
swap :: Array SItem -> SendQueue -> SendQueue
swap items = modify $ set _array items


