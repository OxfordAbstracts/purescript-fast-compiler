module Test.Monad.AffListSpec where

import Test.Prelude

import Control.Monad.Error.Class (catchError)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Test.Monad.AffList as Props
import Webb.AffList (AffList)
import Webb.AffList.Behavior.List as List
import Webb.Monad.Prelude (throwString)


spec :: Spec Unit
spec = describe "Aff list monad" do 
  it "pure value" do 
    let prog = pure 1 :: AffList Int
    listEmits prog [1]
    
  it "appending" do 
    let prog = (pure 1 <> pure 2) <> (pure 3) <> (pure 4)
    listEmits prog [1, 2, 3, 4]
    
  it "empty" do 
    let prog = mempty :: _ Int
    listEmits prog []

  it "mapping" do 
    let prog = (_ + 1) <$> pure 1
    listEmits prog [2]
    
  it "from foldable" do 
    let prog = List.fromFoldable [1, 2, 3, 4]
    listEmits prog [1, 2, 3, 4]
    
  it "apply" do 
    let prog = ado
          a <- List.fromFoldable [1, 2]
          b <- List.fromFoldable [3, 4]
          in a * b
    listEmits prog [3, 4, 6, 8 ]
    
  it "bind" do
    let prog = do 
          a <- List.fromFoldable [1, 2]
          List.fromFoldable [a, a + 10]
    listEmits prog [1, 11, 2, 12]
    
  it "liftEffect" do 
    let prog = do liftEffect (pure 1)
    listEmits prog [1]

  it "liftAff" do 
    let prog = do liftAff (pure 1)
    listEmits prog [1]
    
  it "throwing and catching error" do 
    let prog = do 
          catchError (do 
            a <- List.fromFoldable [1, 2]
            if a == 1 then do
              pure 1
            else do
              throwString "hello"
          ) (\_e -> do
            List.fromFoldable [10, 20] 
          )
    listEmits prog [1, 10, 20]
  
  where
  listEmits = Props.listEmits
  

