module Webb.AffList.Monad.AffList where

import Prelude

import Control.Monad.Error.Class (class MonadError, class MonadThrow, catchError, throwError)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error)
import Webb.AffList.Internal.ListFiber as LFiber
import Webb.AffList.Internal.Node as Node
import Webb.AffList.Monad.Yield (Yield)
import Webb.AffList.Monad.Yield as Yield


{- The AffList monad represents async lists that can yield values. We yield them, 
  and compose new values that are emitted from lists that are created during
  the computation.
  
  One problem here, however, is how we are to go about 'launching' the fiber in the
  context. In the Yield context, using the List has to be done while also installing
  the list fiber as a parent. But the Aff instance allows to bypass this by
  using 'liftAff' and 'runToListFiber'. It's ... hard to be sure what to 
  do about that.

-}

data AffList a = A (Effect (Node.Node a))

instance Semigroup (AffList a) where append = appendImpl
instance Monoid (AffList a) where mempty = memptyImpl
instance Functor AffList where map = mapImpl
instance Apply AffList where apply = applyImpl
instance Applicative AffList where pure = pureImpl
instance Bind AffList where bind = bindImpl
instance Monad AffList
instance MonadThrow Error AffList where throwError = throwErrorImpl
instance MonadError Error AffList where catchError = catchErrorImpl
instance MonadEffect AffList where liftEffect = liftEffectImpl  
instance MonadAff AffList where liftAff = liftAffImpl


runToListFiber :: forall m a. MonadEffect m => AffList a -> m (LFiber.ListFiber a)
runToListFiber (A prog) = liftEffect do 
  node <- prog
  LFiber.newListFiber node

runYieldToList :: forall a. Yield a Unit -> AffList a
runYieldToList prog = A do
  Yield.runToNode prog
  
appendImpl :: forall a. AffList a -> AffList a -> AffList a
appendImpl mx my = runYieldToList do
  xs <- launchList mx
  LFiber.forEach_ xs Yield.yield
  ys <- launchList my
  LFiber.forEach_ ys Yield.yield
  
-- An empty aff list -- when told to receive, will close instead.
memptyImpl :: forall a. AffList a
memptyImpl = runYieldToList do pure unit

-- Implement the map. Instantiate the list, take all of the values, and 
-- emit them in map form.
mapImpl :: forall a b. (a -> b) -> AffList a -> AffList b
mapImpl f list = runYieldToList do
  fiber <- launchList list
  LFiber.forEach_ fiber \a -> do 
    Yield.yield (f a)
  
-- Goes through all the functions, and then through all values, applying each
-- function to _all_ of the list. This can be dangerous -- since there are
-- effects from running the AffList.
applyImpl :: forall a b. AffList (a -> b) -> AffList a -> AffList b
applyImpl mf mx = runYieldToList do 
  fs <- launchList mf
  LFiber.forEach_ fs \f -> do 
    xs <- launchList mx
    LFiber.forEach_ xs \x -> do 
      Yield.yield (f x)
      
pureImpl :: forall a. a -> AffList a
pureImpl a = runYieldToList do Yield.yield a

-- Another kind of 'forEach', except the inner loop is produced at runtime.
bindImpl :: forall a b. AffList a -> (a -> AffList b) -> AffList b
bindImpl mx f = runYieldToList do
  xs <- launchList mx
  LFiber.forEach_ xs \x -> do 
    ys <- launchList (f x)
    LFiber.forEach_ ys \y -> do 
      Yield.yield y
      
throwErrorImpl :: forall a. Error -> AffList a
throwErrorImpl err = runYieldToList do throwError err

catchErrorImpl :: forall a. AffList a -> (Error -> AffList a) -> AffList a
catchErrorImpl mx my = runYieldToList do 
  xs <- launchList mx
  catchError (do 
    LFiber.forEach_ xs Yield.yield 
  ) (\e -> do 
    ys <- launchList (my e)
    LFiber.forEach_ ys Yield.yield
  )
  
liftEffectImpl :: forall a. Effect a -> AffList a
liftEffectImpl prog = runYieldToList do 
  a <- liftEffect prog
  Yield.yield a

liftAffImpl :: forall a. Aff a -> AffList a
liftAffImpl prog = runYieldToList do 
  a <- liftAff prog
  Yield.yield a
  
class LaunchList m where
  launchList :: forall a. AffList a -> m (LFiber.LFiber a)
  
instance LaunchList (Yield.Yield v) where
  launchList list = do 
    fiber <- runToListFiber list
    Yield.addParent fiber -- fiber becomes a parent
    pure fiber
    
-- For anyone else, we simply return the fiber. It is up to the calling context to
-- ensure that if an error occurs while the list has not yet been exhausted, that the list
-- is killed (so that cleanup occurs)
else instance MonadEffect m => LaunchList m where
  launchList list = runToListFiber list