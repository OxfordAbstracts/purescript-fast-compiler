module Webb.AffList.Behavior.List where

import Prelude
import Webb.State.Prelude

import Data.Foldable (class Foldable)
import Data.Foldable as Fold
import Data.Maybe (Maybe(..))
import Webb.AffList.Internal.ListFiber as LFiber
import Webb.AffList.Monad.AffList (AffList, launchList, runYieldToList)
import Webb.AffList.Monad.Yield (yield)
import Webb.Array as Array
import Webb.Stateful (localEffect)


{- Add common list-like behaviors for the AffList. -}
type LBehavior = Unit

-- Take only a few values before stopping.
take :: forall a. Int -> AffList a -> AffList a
take n mx = runYieldToList do
  xs <- launchList mx
  LFiber.while_ xs shouldTake $ \x -> do 
    take_ x

  where
  count = localEffect do newShowRef 0
  take_ x = do 
    (_ + 1) :> count
    yield x
  shouldTake = do 
    i <- aread count
    pure $ i < n

-- Drop only the first 'n' values, and then emit the rest.
drop :: forall a. Int -> AffList a -> AffList a
drop n mx = runYieldToList do 
  xs <- launchList mx
  LFiber.while_ xs shouldDrop $ \x -> do 
    drop_ x
  LFiber.forEach_ xs yield
  where
  count = localEffect do newShowRef 0
  shouldDrop = do 
    i <- aread count
    pure $ i < n
  drop_ _x = do 
    (_ + 1) :> count

-- Take all items satisfying the condition, but no more than that. Note that this 
-- necessarily means the first non-matching item will be computed, even if this has effects.
takeWhile :: forall a. (a -> Boolean) -> AffList a -> AffList a
takeWhile f mx = runYieldToList do 
  xs <- launchList mx
  LFiber.while_ xs shouldTake $ take_
  where
  continue = localEffect do newShowRef true
  shouldTake = aread continue
  take_ x = do 
    continue := f x
    whenM (aread continue) do 
      yield x
      
-- We drop while items exist to be dropped, and then emit the rest.
dropWhile :: forall a. (a -> Boolean) -> AffList a -> AffList a
dropWhile f mx = runYieldToList do 
  xs <- launchList mx
  LFiber.while_ xs shouldDrop $ drop_
  yieldLast
  LFiber.forEach_ xs yield

  where
  last = localEffect do newShowRef Nothing
  continue = localEffect do newShowRef true
  shouldDrop = aread continue
  drop_ x = do 
    continue := f x
    last := Just x
  yieldLast = do 
    mval <- aread last
    Fold.for_ mval yield
  
fromFoldable :: forall f a. Foldable f => f a -> AffList a
fromFoldable ma = runYieldToList do
  Fold.for_ array yield
  where
  array = Array.fromFoldable ma
  
-- Fold the values. Should _avoid_ accumulating a collection, since the list might
-- be infinite.
foldl :: forall a b. (b -> a -> b) -> b -> AffList a -> AffList b
foldl f init mx = runYieldToList do 
  xs <- launchList mx
  LFiber.forEach_ xs combine
  yieldAcc
  where
  acc = localEffect $ newShowRef init
  combine x = do flip f x :> acc
  yieldAcc = do 
    result <- aread acc
    yield result
  
-- Scan the values, emitting an item for each combination
scanl :: forall a b. (b -> a -> b) -> b -> AffList a -> AffList b
scanl f init mx = runYieldToList do 
  xs <- launchList mx
  LFiber.forEach_ xs combineAndYield
  where
  acc = localEffect $ newShowRef init
  combineAndYield x = do 
    flip f x :> acc
    result <- aread acc
    yield result
    
filter :: forall a. (a -> Boolean) -> AffList a -> AffList a
filter f mx = runYieldToList do 
  xs <- launchList mx
  LFiber.forEach_ xs \x -> do 
    when (f x) do yield x
  
reject :: forall a. (a -> Boolean) -> AffList a -> AffList a
reject f mx = filter (not <<< f) mx

-- Group the outputs into lists of at most 'n'
groupN :: forall a. Int -> AffList a -> AffList (Array a)
groupN n mx = runYieldToList do 
  xs <- launchList mx
  LFiber.forEach_ xs \x -> do
    groupAndYield x
  flush
  where
  items = localEffect $ newShowRef []
  groupAndYield x = do 
    Array.addLast x :> items
    len <- Array.size <: items
    when (len >= n) do
      array <- aread items
      items := []
      yield array
  flush = do 
    array <- aread items
    unless (Array.isEmpty array) do 
      yield array
      