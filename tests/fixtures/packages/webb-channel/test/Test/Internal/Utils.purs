module Test.Internal.Utils where

import Test.Prelude
import Webb.State.Prelude

import Effect.Aff (Aff)
import Unsafe.Coerce (unsafeCoerce)
import Webb.Channel.Data.Id as Id
import Webb.Channel.Data.ReceiveItem as RItem
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Channel.Data.SendItem as SItem
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.State (CState)
import Webb.Channel.Internal.State as State
import Webb.Result as Result

sitem :: Int -> Aff SItem.SItem
sitem i = do
  result <- Result.newResult
  let id = Id.fromInt i
  let value = i
  pure $ SItem.newItem value id result
  
ritem :: Int -> Aff RItem.RItem
ritem i = do 
  result <- Result.newResult
  let id = Id.fromInt i
  pure $ RItem.newItem id result
  
unvoidInt :: Void -> Int
unvoidInt = unsafeCoerce

buffer :: State.CState -> Aff (Array Int)
buffer state = do
  items <- SQueue.buffer <: state.senders
  pure $ svalue <$> items

senders :: State.CState -> Aff (Array Int)
senders state = do
  items <- SQueue.toArray <: state.senders
  pure $ svalue <$> items
  
svalue :: SItem.SItem -> Int
svalue item = let
  value = SItem.value item
  in unvoidInt value

bufferIs :: CState -> Array Int -> Aff Unit
bufferIs this ints = do
  arr <- buffer this
  arr === ints
  
sendersIs :: CState -> Array Int -> Aff Unit
sendersIs this ints = do
  arr <- senders this
  arr === ints
  
receiveCountIs :: CState -> Int -> Aff Unit
receiveCountIs this i = do
  size <- RQueue.size <: this.receivers
  size === i

sendCountIs :: CState -> Int -> Aff Unit
sendCountIs this i = do
  size <- SQueue.size <: this.senders
  size === i


