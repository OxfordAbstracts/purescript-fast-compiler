module Webb.Stateful.ArrayColl where

import Prelude
import Webb.State.Prelude

import Data.Array as A
import Data.Maybe (Maybe)
import Data.Traversable (for)
import Effect.Class (class MonadEffect, liftEffect)
import Webb.Monad.Prelude (forceMaybe')
import Webb.Stateful (defaultCompare, defaultEq)


newtype ArrayColl a = AC (ShowRef (Array a))

derive newtype instance Show a => Show (ArrayColl a)
derive newtype instance Refer (Array a) (ArrayColl a)

instance Eq a => Eq (ArrayColl a) where
  eq = defaultEq

instance Ord a => Ord (ArrayColl a) where
  compare = defaultCompare
  
newArray :: forall a m. MonadEffect m => m (ArrayColl a)
newArray = do
  ref <- newShowRef []
  pure $ AC ref

newArray' :: forall a m. MonadEffect m => Array a -> m (ArrayColl a)
newArray' arr = do
  ref <- newShowRef arr
  pure $ AC ref
    
addLast :: forall a m. MonadEffect m => ArrayColl a -> a -> m Unit
addLast (AC ref) a = flip A.snoc a :> ref

addFirst :: forall a m. MonadEffect m => ArrayColl a -> a -> m Unit
addFirst (AC ref) a = A.cons a :> ref

addAllLast :: forall a m. MonadEffect m => ArrayColl a -> Array a -> m Unit
addAllLast (AC ref) arr = (_ <> arr) :> ref

addAllFirst :: forall a m. MonadEffect m => ArrayColl a -> Array a -> m Unit
addAllFirst (AC ref) arr = (arr <> _) :> ref

clear :: forall a m. MonadEffect m => ArrayColl a -> m (Array a)
clear coll = do
  removed <- aread coll
  awrite [] coll
  pure removed

clear_ :: forall a m. MonadEffect m => ArrayColl a -> m Unit
clear_ coll = void $ clear coll

removeFirst :: forall a m. MonadEffect m => ArrayColl a -> m (Maybe a)
removeFirst coll = do 
  removed <- removeFirstN coll 1
  pure $ A.head removed

removeFirst_ :: forall a m. MonadEffect m => ArrayColl a -> m Unit
removeFirst_ coll = void $ removeFirst coll

removeFirstN :: forall a m. MonadEffect m => ArrayColl a -> Int -> m (Array a)
removeFirstN coll n = do 
  removed <- A.take n <: coll
  A.drop n :> coll
  pure removed

removeFirstN_ :: forall a m. MonadEffect m => ArrayColl a -> Int -> m Unit
removeFirstN_ coll n = void $ removeFirstN coll n

removeLast :: forall a m. MonadEffect m => ArrayColl a -> m (Maybe a)
removeLast coll = do 
  removed <- removeLastN coll 1
  pure $ A.last removed

removeLast_ :: forall a m. MonadEffect m => ArrayColl a -> m Unit
removeLast_ coll = void $ removeLast coll

removeLastN :: forall a m. MonadEffect m => ArrayColl a -> Int -> m (Array a)
removeLastN coll n = do 
  removed <- A.takeEnd n <: coll
  A.dropEnd n :> coll
  pure removed

removeLastN_ :: forall a m. MonadEffect m => ArrayColl a -> Int -> m Unit
removeLastN_ coll n = void $ removeLastN coll n
  
-- Search and remove the item wherever it occurs.
removeEq :: forall a m. MonadEffect m => Eq a => ArrayColl a -> a -> m Unit
removeEq coll a = filter coll (_ == a)
  
filter :: forall a m. MonadEffect m => ArrayColl a -> (a -> Boolean) -> m Unit
filter coll f = do A.filter f :> coll

forEach :: forall a b m. MonadEffect m => ArrayColl a -> (a -> m b) -> m (Array b)
forEach coll f = do
  arr :: Array a <- aread coll
  for arr f

forEach_ :: forall a b m. MonadEffect m => ArrayColl a -> (a -> m b) -> m Unit
forEach_ coll f = void $ forEach coll f

length :: forall a m. MonadEffect m => ArrayColl a -> m Int
length coll = areads A.length coll

index :: forall a m. MonadEffect m => ArrayColl a -> Int -> m (Maybe a)
index coll i = (\arr -> A.index arr i) <: coll

unsafeIndex :: forall a m. MonadEffect m => ArrayColl a -> Int -> m a
unsafeIndex coll i = liftEffect do  
  ma :: Maybe a <- index coll i
  forceMaybe' ("Out of bounds: " <> show i) ma