module Test.Data.SendQueueSpec where

import Test.Prelude

import Data.Traversable (class Foldable, sequence)
import Effect.Aff (Aff)
import Unsafe.Coerce (unsafeCoerce)
import Webb.Array as Array
import Webb.Channel.Data.Id as Id
import Webb.Channel.Data.SendItem as SItem
import Webb.Channel.Data.SendQueue (SQueue)
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Monad.Prelude (forceMaybe')
import Webb.Result as Result


spec :: Spec Unit
spec = describe "Send queue data" do 
  it "empty" do 
    q <- new 0 []
    queueIs q []
    
  it "not empty" do 
    q <- new 0 [1, 2]
    queueIs q [1, 2]
    
  it "can check if empty" do 
    q <- new 0 []
    isEmpty q true

    q1 <- new 0 [1]
    isEmpty q1 false
    
    q2 <- new 1 []
    isEmpty q2 true

    q3 <- new 1 [2]
    isEmpty q3 false
    
  it "can check if full" do 
    q <- new 0 []
    isFull q true

    q1 <- new 0 [1]
    isFull q1 true
    
    q2 <- new 1 []
    isFull q2 false

    q3 <- new 1 [2]
    isFull q3 true
    
  it "can remove pending ids" do 
    q <- new 0 [1, 2, 3, 4]
    let q1 = removeId q 3
    queueIs q1 [1, 2, 4]
    
  it "add/remove operations" do 
    q <- new 2 [1, 2, 3]
    q1 <- addLast 4 q
    q2 <- drop 2 q1

    queueIs q1 [1, 2, 3, 4]
    firstIs q1 1

    queueIs q2 [3, 4]
    firstIs q2 3
    
  it "view pending" do 
    q <- new 0 [1, 2, 3]
    pendingIs q [1, 2, 3]
    
    q1 <- new 2 [1, 2, 3]
    pendingIs q1 [3]
    
    -- An infinite buffer never has any pending items.
    q2 <- newInf [1, 2, 3]
    pendingIs q2 []

  it "remove pending" do 
    q <- removePending <$> new 1 [1, 2, 3]
    pendingIs q []
    queueIs q [1]
    
    q1 <- removePending <$> new 2 [1, 2, 3]
    pendingIs q1 []
    queueIs q1 [1, 2]
    
    q2 <- removePending <$> newInf [1, 2, 3]
    pendingIs q2 []
    queueIs q2 [1, 2, 3]

  where
  firstIs q i = do
    let mfirst = SQueue.first q
    first <- forceMaybe' "No first" mfirst
    integer first === i

  removePending :: SQueue -> SQueue
  removePending q = SQueue.removePending q

  pendingIs q ints = do
    let pending = SQueue.pending q
    integers pending === ints

  drop n q = do 
    pure $ SQueue.drop n q

  addLast i q = do
    item <- mkItem i
    pure $ SQueue.addLast item q
  
  removeId q i = let 
    id = Id.fromInt i
    in SQueue.removeId id q
    
  integers :: forall f. Foldable f => f SItem.SItem -> Array Int
  integers f = let 
    arr = Array.fromFoldable f
    in (unvoidInt <<< SItem.value) <$> arr

  integer :: SItem.SItem -> Int
  integer item = (unvoidInt <<< SItem.value) item
  
  isEmpty :: SQueue -> Boolean -> Aff Unit
  isEmpty q flag = do 
    SQueue.isEmpty q === flag

  isFull :: SQueue -> Boolean -> Aff Unit
  isFull q flag = do 
    SQueue.isFull q === flag

  new :: Int -> Array Int -> Aff SQueue.SQueue
  new size ints = do
    items <- sequence (mkItem <$> ints)
    pure $ SQueue.fromArray (SQueue.Finite size) items
    
  newInf :: Array Int -> Aff SQueue.SQueue
  newInf ints = do 
    items <- sequence (mkItem <$> ints)
    pure $ SQueue.fromArray (SQueue.Infinite) items
    
  mkItem :: Int -> Aff SItem.SItem
  mkItem i = do
    let id = Id.fromInt i
    result <- Result.newResult
    let item = SItem.newItem i id result
    pure item
    
  queueIs :: SQueue.SQueue -> Array Int -> Aff Unit
  queueIs q arr = do
    let items = SQueue.toArray q
        values = unvoidInt <<< SItem.value <$> items
    values === arr
    
  unvoidInt :: Void -> Int
  unvoidInt = unsafeCoerce

    
