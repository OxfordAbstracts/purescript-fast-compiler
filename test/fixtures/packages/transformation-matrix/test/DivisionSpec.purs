module Test.DivisionSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Data.Either (Either(..))
import Data.TransformationMatrix.Division (divide)
import Data.TransformationMatrix.DivisionError (DivisionError(..))

divisionSpec :: Spec Unit
divisionSpec = do
  describe "DivisionSpec" do
    it "should divide" do
      let
        -- Expectation
        expectedResult = Right 2.5
        
        -- Test
        result = divide 5.0 2.0
      result `shouldEqual` expectedResult

    it "should gracefully fail division by zero" do
      let
        -- Expectation
        expectedResult = Left DivideByZero 
        
        -- Test
        result = divide 5.0 0.0
      result `shouldEqual` expectedResult