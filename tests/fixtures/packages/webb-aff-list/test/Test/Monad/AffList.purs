module Test.Monad.AffList where

import Test.Prelude

import Effect.Aff (Aff)
import Webb.AffList as LFiber
import Webb.AffList.Monad.AffList (AffList)
import Webb.AffList.Monad.AffList as AffList
import Webb.Stateful (localEffect)


type AffListProps = Unit

listEmits :: forall a. Eq a => Show a => AffList a -> Array a -> Aff Unit
listEmits list ints = do 
  fiber <- AffList.launchList list
  LFiber.forEach_ fiber take
  taken ?= ints
  
  where
  ref = localEffect $ newShowRef []
  take x = (_ <> [x]) :> ref
  taken = aread ref