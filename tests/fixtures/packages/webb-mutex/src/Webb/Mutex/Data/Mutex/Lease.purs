module Webb.Mutex.Data.Mutex.Lease where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, isJust, isNothing)
import Data.Newtype (class Newtype, unwrap, wrap)
import Webb.Mutex.Data.Mutex.Id (Id)
import Webb.Mutex.Data.Mutex.Item (Item)
import Webb.Mutex.Data.Mutex.Item as Item


{- Represent the lease state. Owned, or not owned? If owned, by whom?
-}

newtype Lease = O (Maybe Lease_)

derive newtype instance Eq Lease
derive newtype instance Ord Lease
derive newtype instance Show Lease
derive instance Newtype Lease _

type Lease_ =
  { id :: Id
  , name :: Maybe String
  }
  
none :: Lease 
none = wrap Nothing

newLease :: Id -> Maybe String -> Lease 
newLease t n = wrap (Just { id: t, name: n })

newLease' :: Id -> Lease 
newLease' t = wrap (Just { id: t, name: Nothing })

fromItem :: Item -> Lease
fromItem item = newLease (Item.tag item) (Item.name item)

owner :: Lease -> Maybe Lease_
owner = unwrap

id :: Lease -> Maybe Id
id o = do 
  s <- owner o
  pure $ s.id

name :: Lease -> Maybe String
name o = do 
  s <- owner o
  s.name
  
isNone :: Lease -> Boolean
isNone = unwrap >>> isNothing

isOwned :: Lease -> Boolean
isOwned = unwrap >>> isJust

isOwnedBy :: String -> Lease -> Boolean
isOwnedBy n lease = fromMaybe false do
  n' <- name lease
  pure $ n == n'
  
hasId :: Id -> Lease -> Boolean
hasId t lease = fromMaybe false do
  t' <- id lease 
  pure $ t == t'