module Test.Data.Mutex.ItemSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Item as Item
import Webb.Result as Result



spec :: Spec Unit
spec = describe "Item data" do 
  it "getters" do
    item <- newItem 3 "bob"
    idIs item 3
    nameIs item "bob"
    
  it "has tag or name" do 
    item <- newItem 3 "bob"
    hasName item "bob"
    hasTag item 3
    
  

  where
  hasName item i = do
    Item.hasName i item === true
    
  hasTag item i = do
    Item.hasTag (Id.fromInt i) item === true
  
  idIs item i = do
    let int = Id.toInt $ Item.tag item
    int === i
    
  nameIs item s = do
    let name = Item.name item
    name === Just s

  newItem i string = do
    result <- Result.newResult
    let item = Item.newItem (Id.fromInt i) (Just string) result
    pure item
