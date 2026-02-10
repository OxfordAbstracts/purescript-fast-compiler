module Webb.Mutex.Internal.Mutex.Locker where

import Prelude
import Webb.State.Prelude

import Data.Maybe (Maybe, fromMaybe)
import Data.Newtype (class Newtype, unwrap)
import Effect.Aff (Aff)
import Webb.Mutex.Data.Mutex.Id (Id)
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Lease as Lease
import Webb.Mutex.Internal.Mutex.State (MutexState)
import Webb.Mutex.Internal.Mutex.State as State
import Webb.Monad.Prelude (expect)


{- Responsible for the concept of locking the mutex. Transient; not meant to 
persist. 
-}

newtype Locker = L MutexState

derive instance Newtype Locker _

newLocker :: MutexState -> Locker
newLocker state = L state

getThis :: Locker -> Aff MutexState
getThis = unwrap >>> pure

isLocked :: Locker -> Aff Boolean
isLocked l = do 
  this <- getThis l
  State.isLocked this

isLockedByName :: Locker -> String -> Aff Boolean
isLockedByName l name = do 
  this <- getThis l
  State.isLockedByName this name

isLockedById :: Locker -> Id -> Aff Boolean
isLockedById l id = do 
  this <- getThis l
  State.isLockedById this id
  
-- Attempt to lock with the given name, and return whether it succeeded.
-- If re-entering with the same name, throw an error.
lock :: Locker -> Maybe String -> Aff Boolean
lock l mname = do
  checkOwner
  this <- getThis l
  alreadyLocked <- isLocked l
  if alreadyLocked then do
    pure false 
  else do
    newLease <- getNewLease
    this.lease := newLease
    pure true
    
  where
  checkOwner = do
    this <- getThis l
    ownerName <- Lease.name <: this.lease
    let sameName = fromMaybe false do
          n1 <- ownerName
          n2 <- mname
          pure $ n1 == n2
    expect (not sameName) $ "Attempted to re-enter lock: " <> show mname
    
  getNewLease = do
    -- We use the previous id for a new, immediate lease.
    -- This works because we have no competitors.
    this <- getThis l
    id <- Id.prev <: this.id 
    Id.next :> this.id
    let lease = Lease.newLease id mname
    pure lease
  

