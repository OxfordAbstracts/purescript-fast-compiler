module Webb.State.Prelude where

import Prelude

import Control.Monad.Except (ExceptT, lift)
import Control.Monad.Identity.Trans (IdentityT)
import Control.Monad.Maybe.Trans (MaybeT)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (State, StateT, runState)
import Control.Monad.State as S
import Control.Monad.Writer (WriterT)
import Data.Lens (Lens', view)
import Data.Tuple (Tuple(..))
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Ref (Ref, new, read, write)
import Effect.Unsafe (unsafePerformEffect)

newtype ShowRef s = S (Ref s)

derive newtype instance Refer s (ShowRef s)

instance Show s => Show (ShowRef s) where
  show (S ref) = show $ unsafePerformEffect do (aread ref)

instance Eq s => Eq (ShowRef s) where
  eq (S a) (S b) = unsafePerformEffect do
    a' <- aread a
    b' <- aread b
    pure $ a' == b'

newRef :: forall m s. MonadEffect m => s -> m (Ref s)
newRef s = liftEffect do new s

newShowRef :: forall m s. MonadEffect m => s -> m (ShowRef s)
newShowRef s = liftEffect do 
  ref <- newRef s
  pure $ S ref

class Refer s r | r -> s where
  aread :: forall m. MonadEffect m => r -> m s
  awrite :: forall m. MonadEffect m => s -> r -> m Unit
  
instance Refer s (Ref s) where
  aread r = liftEffect $ read r
  awrite s r = liftEffect $ write s r
  
areads :: forall m r s a. MonadEffect m => Refer s r => (s -> a) -> r -> m a
areads f r = do
  s <- aread r
  pure $ f s

amodify_ :: forall m r s. MonadEffect m => Refer s r => (s -> s) -> r -> m Unit
amodify_ f r = void $ amodify f r

amodify :: forall m r s. MonadEffect m => Refer s r => (s -> s) -> r -> m s
amodify f r = do 
  s <- aread r
  let s' = f s
  awrite s' r 
  pure s'
  

-- Operators to read from, or modify, a Ref
infix 5 areads as <:
infix 5 fwrite as :=
infix 5 amodify_ as :>

fread :: forall m r s. MonadEffect m => Refer s r => r -> m s
fread = aread

freads :: forall m r s a. MonadEffect m => Refer s r => r -> (s -> a) -> m a
freads = flip areads

fmodify_ :: forall m r s. MonadEffect m => Refer s r => r -> (s -> s) -> m Unit
fmodify_ = flip amodify_

fmodify :: forall m r s. MonadEffect m => Refer s r => r -> (s -> s) -> m s
fmodify = flip amodify

fwrite :: forall m r s. MonadEffect m => Refer s r => r -> s -> m Unit
fwrite = flip awrite

modifyAndWrite :: forall m r s a. MonadEffect m => Refer s r =>
  (s -> (Tuple a s)) -> r -> m a
modifyAndWrite f ref = do
  Tuple a newState <- areads f ref
  awrite newState ref
  pure a

infix 5 modifyAndWrite as :=>

class Monad m <= ReferM s m | m -> s where
  mread :: m s
  mwrite :: s -> m Unit
  
instance Monad m => ReferM s (StateT s m) where
  mread = S.get
  mwrite = S.put
  
mreads :: forall m s a. ReferM s m => (s -> a) -> m a
mreads f = do
  s <- mread
  pure $ f s

mmodify_ :: forall m s. ReferM s m => (s -> s) -> m Unit
mmodify_ f = void $ mmodify f

mmodify :: forall m s. ReferM s m => (s -> s) -> m s
mmodify f = do
  s <- mread
  let new = f s
  mwrite new
  pure new
  
views :: forall a b r. Lens' r a -> (a -> b) -> r -> b
views l f r = f (view l r)

applyState :: forall m r s a. MonadEffect m => Refer s r =>
  State s a -> r -> m a
applyState prog ref = do
  state <- aread ref
  let Tuple a newState = runState prog state
  awrite newState ref
  pure a

applyStateFlipped :: forall m r s a. MonadEffect m => Refer s r =>
  r -> State s a -> m a
applyStateFlipped = flip applyState
  
infix 5 applyState as :>>
infix 5 applyStateFlipped as <<:


instance ReferM s m => ReferM s (ExceptT e m) where
  mread = lift mread
  mwrite s = lift $ mwrite s

instance ReferM s m => ReferM s (MaybeT m) where
  mread = lift mread
  mwrite s = lift $ mwrite s

instance ReferM s m => ReferM s (ReaderT r m) where
  mread = lift mread
  mwrite s = lift $ mwrite s

instance (Monoid r, ReferM s m) => ReferM s (WriterT r m) where
  mread = lift mread
  mwrite s = lift $ mwrite s

instance (ReferM s m) => ReferM s (IdentityT m) where
  mread = lift mread
  mwrite s = lift $ mwrite s

