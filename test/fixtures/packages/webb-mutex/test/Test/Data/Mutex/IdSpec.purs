module Test.Data.Mutex.IdSpec where

import Test.Prelude

import Webb.Mutex.Data.Mutex.Id as Id


spec :: Spec Unit
spec = describe "Id operations" do
  it "base id is 0" do
    let id = Id.initial
    idIs id 0
    
  it "previous is -1" do
    let id = Id.prev $ Id.initial
    idIs id (-1)
    
  it "next is 1" do
    let id = Id.next $ Id.initial
    idIs id (1)

  where
  idIs id int = do
    let i = Id.toInt id
    i === int
