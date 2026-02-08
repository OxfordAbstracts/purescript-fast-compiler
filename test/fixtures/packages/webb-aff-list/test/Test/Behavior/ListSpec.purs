module Test.Behavior.ListSpec where

import Test.Prelude

import Data.Int (even)
import Test.Behavior.List as Props
import Test.Monad.AffList as AListProps
import Webb.AffList.Behavior.List as List


spec :: Spec Unit
spec = describe "List-like monads" do 
  it "take" do 
    let prog = List.take 2 (List.fromFoldable [1, 2, 3])
    listEmits prog [1, 2]

  it "drop" do 
    let prog = List.drop 2 (List.fromFoldable [1, 2, 3])
    listEmits prog [3]
    
  it "take while" do 
    let prog = List.takeWhile (_ < 3) (List.fromFoldable [1, 2, 3])
    listEmits prog [1, 2]

  it "drop while" do 
    let prog = List.dropWhile (_ < 3) (List.fromFoldable [1, 2, 3, 4])
    listEmits prog [3, 4]
    
  it "foldl" do 
    let prog = List.foldl (+) 0 (List.fromFoldable [1, 2, 3])
    listEmits prog [6]

  it "scanl" do 
    let prog = List.scanl (+) 0 (List.fromFoldable [1, 2, 3])
    listEmits prog [1, 3, 6]
    
  it "filter" do 
    let prog = List.filter (even) (List.fromFoldable [1, 2, 3, 4])
    listEmits prog [2, 4]

  it "reject" do 
    let prog = List.reject (even) (List.fromFoldable [1, 2, 3, 4])
    listEmits prog [1, 3]
    
  it "group by n" do 
    let prog = List.groupN 2 (List.fromFoldable [1, 2, 3, 4, 5])
    listEmits prog [[1, 2], [3, 4], [5]]
    
  where
  listEmits = AListProps.listEmits