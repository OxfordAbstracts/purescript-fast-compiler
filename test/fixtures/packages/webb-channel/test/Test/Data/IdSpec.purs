module Test.Data.IdSpec where

import Test.Prelude

import Webb.Channel.Data.Id as Id


spec :: Spec Unit
spec = describe "Id data" do 
  it "is initially 0" do 
    let id = Id.initial
    idIs id 0
    
  it "can get next" do 
    let id = Id.next Id.initial
    idIs id 1

  it "can get prev" do 
    let id = Id.prev Id.initial
    idIs id (-1)
    
  where
  idIs id int = do
    Id.toInt id === int
