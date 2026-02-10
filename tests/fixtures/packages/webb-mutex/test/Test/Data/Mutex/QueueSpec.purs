module Test.Data.Mutex.QueueSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Item as Item
import Webb.Mutex.Data.Mutex.Queue as Queue
import Webb.Result as Result
import Webb.Stateful (localEffect)


spec :: Spec Unit
spec = describe "queue" do 
  it "empty queue" do
    let queue = Queue.empty
    queueIdsAre queue []
    queueNamesAre queue []
    
  it "enqueue" do
    let queue = Queue.empty # enqueue 1 >>> enqueue 2
    queueIdsAre queue [1, 2]
    sizeIs queue 2
    
  it "peek" do 
    let queue = Queue.empty # enqueue 1
    peekIs queue 1
    let queue' = queue # enqueue 2
    queueIdsAre queue [1]
    peekIs queue' 1
    sizeIs queue' 2
    
  it "dequeue" do
    let queue = Queue.empty # enqueue 1 >>> enqueue 2
    queueIdsAre queue [1, 2]
    let queue' = Queue.dequeue queue
    queueIdsAre queue' [2]
    
  it "remove id" do 
    let queue = Queue.empty # enqueue 1 >>> enqueue 2 >>> enqueue 3
        id = Id.fromInt 2
        queue' = Queue.removeId id queue
    queueIdsAre queue' [1, 3]
    
  where
  peekIs queue i = do
    let int = do 
          item <- Queue.peek queue
          pure $ item # Item.tag >>> Id.toInt
    int === Just i       
    
  sizeIs queue i = do
    let size = Queue.size queue
    size === i
  
  enqueue i queue = localEffect do
    let id = Id.fromInt i
    result <- Result.newResult
    let item = Item.newItem id Nothing result
    pure $ Queue.enqueue item queue

  queueIdsAre queue arr = do
    let queueArr = Queue.toArray queue
        ids = (Item.tag >>> Id.toInt) <$> queueArr
    ids === arr

  queueNamesAre queue arr = do
    let queueArr = Queue.toArray queue
        names = Item.name <$> queueArr
    names === arr
