module Webb.AffList 
( module P
, AList
, withList
)
where

import Prelude

import Effect.Aff (Aff)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff, liftAff)
import Webb.AffList.Behavior.List (take, drop, takeWhile, dropWhile, fromFoldable, foldl, scanl, filter, reject, groupN) as P
import Webb.Channel.Data.CMaybe (CMaybe(..)) as P
import Webb.AffList.Internal.ListFiber (ListFiber, LFiber, kill, receive, receive', forEach_, while_) as P
import Webb.AffList.Internal.ListFiber as LFiber
import Webb.AffList.Internal.ListFiber (LFiber)
import Webb.AffList.Monad.AffList (AffList)
import Webb.AffList.Monad.AffList (AffList, runYieldToList, class LaunchList, launchList) as P
import Webb.AffList.Monad.AffList as AffList
import Webb.AffList.Monad.Yield (Yield, addParent, finally, onCancel, asAff) as P

{-
The AffList provides all methods needed to work with the AffList.
-}

type AList = AffList

withList :: forall m x a. MonadAff m => AList x -> (LFiber x -> Aff a) -> m a
withList mx f = liftAff do 
  xs <- AffList.launchList mx
  Aff.finally (do 
    LFiber.kill xs
  ) (do 
    f xs 
  )