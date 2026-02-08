module Test.Data.Mutex.LeaseSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Lease as Lease



spec :: Spec Unit
spec = describe "Lease ownership" do
  it "empty lease" do
    let lease = Lease.none
    isOwned lease false
    isOwnedBy lease "bob" false
    hasId lease 1 false
    
  it "new lease" do 
    let lease = newLease 2 "bob"
    isOwned lease true

    isOwnedBy lease "bob" true
    hasId lease 2 true

    isOwnedBy lease "bobi" false
    hasId lease 3 false
    
  where
  newLease i s = Lease.newLease (Id.fromInt i) (Just s)

  isOwned lease flag = do
    Lease.isOwned lease === flag
    
  isOwnedBy lease string flag = do
    Lease.isOwnedBy string lease === flag
    
  hasId lease i flag = do
    Lease.hasId (Id.fromInt i) lease === flag
