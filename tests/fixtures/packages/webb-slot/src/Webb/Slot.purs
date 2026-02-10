module Webb.Slot where

import Prelude

import Data.Maybe (Maybe(..), isNothing)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Ref (Ref)
import Effect.Unsafe (unsafePerformEffect)
import Webb.Monad.Prelude (forceMaybe')
import Webb.State.Prelude (class Refer, aread, awrite, newRef)

{- A slot for dependencies that must be added at runtime. Will error if
  not present, yet requested.
-}

newtype Slot a = S_ { name :: String, ref :: (Ref (Maybe a)) }

newSlot :: forall m a. MonadEffect m => String -> m (Slot a)
newSlot name = do
  ref <- newRef (Nothing)
  pure $ S_ { name, ref }
  
-- Can always write a value
instance Refer a (Slot a) where
  awrite v (S_ { ref }) = do awrite (pure v) ref
  aread (S_ { ref, name }) = liftEffect do 
    mval <- aread ref
    forceMaybe' ("Slot is empty: " <> name) mval
    
instance Show a => Show (Slot a) where
  show (S_ s) = unsafePerformEffect do 
    mval <- aread s.ref
    case mval of 
      Nothing -> do 
        pure $ "Slot \"" <> s.name <> "\" (empty)"
      Just val -> do 
        pure $ show val

clear :: forall m a. MonadEffect m => Slot a -> m Unit
clear (S_ { ref }) = do awrite Nothing ref

isEmpty :: forall m a. MonadEffect m => Slot a -> m Boolean
isEmpty (S_ { ref }) = do
  a <- aread ref
  pure $ isNothing a