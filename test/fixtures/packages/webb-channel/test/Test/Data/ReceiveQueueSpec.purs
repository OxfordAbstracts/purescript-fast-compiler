module Test.Data.ReceiveQueueSpec where

import Test.Prelude

import Data.Traversable (sequence)
import Effect.Aff (Aff)
import Webb.Channel.Data.Id as Id
import Webb.Channel.Data.ReceiveItem (RItem)
import Webb.Channel.Data.ReceiveItem as RItem
import Webb.Channel.Data.ReceiveQueue (RQueue)
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Result as Result

spec :: Spec Unit
spec = describe "ReceiveQueue data" do 
  it "empty" do
    q <- new []
    queueIs q []
    isEmpty q true
    
  it "not empty" do 
    q <- new [1, 2, 3]
    queueIs q [1, 2, 3]
    isEmpty q false
    
  it "can remove id" do 
    q <- removeId 3 <$> new [1, 2, 3, 4]
    queueIs q [1, 2, 4]
    
  it "can add/remove" do 
    q <- new [1, 2]
    q1 <- addLast 3 q
    q2 <- drop 2 q1
    
    queueIs q1 [1, 2, 3]
    sizeIs q1 3
    queueIs q2 [3]
    sizeIs q2 1
    
  where
  sizeIs q n = do
    RQueue.size q === n

  drop n q = do 
    pure $ RQueue.drop n q

  addLast i q = do
    item <- mkItem i
    pure $ RQueue.addLast item q

  removeId i = RQueue.removeId (Id.fromInt i)
  
  isEmpty q flag = do
    RQueue.isEmpty q === flag
  
  queueIs q ints = do 
    integers q === ints
    
  integers :: RQueue -> Array Int
  integers queue = let 
    items = RQueue.toArray queue
    ids = Id.toInt <<< RItem.id <$> items
    in ids

  new :: Array Int -> Aff RQueue
  new arr = do 
    items <- sequence (mkItem <$> arr)
    pure $ RQueue.fromArray items
    
  mkItem :: Int -> Aff RItem
  mkItem i = do 
    result <- Result.newResult
    let id = Id.fromInt i
        item = RItem.newItem id result
    pure item
