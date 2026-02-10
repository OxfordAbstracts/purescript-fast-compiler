module Test.Matrix4Spec where

import Prelude hiding (add)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Data.TransformationMatrix.Vector3 (Vector3(..))
import Data.TransformationMatrix.Matrix4 
  ( Matrix4(..)
  , translate
  , toArray
  , getPosition
  , setPosition
  , scale )

matrix4Spec :: Spec Unit
matrix4Spec = do
  describe "Matrix4Spec" do
    it "should convert a Matrix4 to an array" do
      let
        -- Setup 
        matrix = Matrix4
          1.0 0.0 0.0 1.0
          0.0 1.0 0.0 2.0
          0.0 0.0 1.0 3.0
          0.0 0.0 0.0 1.0

        -- Expectations
        expectedResult =
          [ 1.0, 0.0, 0.0, 1.0
          , 0.0, 1.0, 0.0, 2.0
          , 0.0, 0.0, 1.0, 3.0
          , 0.0, 0.0, 0.0, 1.0 ]
      
        -- Test
        result = toArray matrix
      result `shouldEqual` expectedResult

    it "should get the position of a Matrix4" do
      let
        -- Setup 
        matrix = Matrix4
          1.0 0.0 0.0 1.0
          0.0 1.0 0.0 2.0
          0.0 0.0 1.0 3.0
          0.0 0.0 0.0 1.0

        -- Expectations
        expectedResult = Vector3 1.0 2.0 3.0

        -- Test
        result = getPosition matrix
      result `shouldEqual` expectedResult

    it "should set the position of a Matrix4" do
      let
        -- Setup 
        matrix = Matrix4
          1.0 0.0 0.0 1.0
          0.0 1.0 0.0 2.0
          0.0 0.0 1.0 3.0
          0.0 0.0 0.0 1.0
        position = Vector3 4.0 5.0 6.0

        -- Expectations
        expectedResult = Matrix4
          1.0 0.0 0.0 4.0
          0.0 1.0 0.0 5.0
          0.0 0.0 1.0 6.0
          0.0 0.0 0.0 1.0

        -- Test
        result = setPosition position matrix
      result `shouldEqual` expectedResult

    it "should translate a Matrix4" do
      let
        -- Setup
        matrix = Matrix4
          1.0 0.0 0.0 1.0
          0.0 1.0 0.0 2.0
          0.0 0.0 1.0 3.0
          0.0 0.0 0.0 1.0
        translation = Vector3 2.0 3.0 4.0
      
        -- Expectations
        expectedResult = Matrix4
          1.0 0.0 0.0 3.0
          0.0 1.0 0.0 5.0
          0.0 0.0 1.0 7.0
          0.0 0.0 0.0 1.0
        
        -- Test
        result = translate translation matrix
      result `shouldEqual` expectedResult
    
    it "should scale a Matrix4" do
      let
        -- Setup
        matrix = Matrix4
          1.0 0.0 0.0 1.0
          0.0 1.0 0.0 2.0
          0.0 0.0 1.0 3.0
          0.0 0.0 0.0 1.0
        multiplier = 2.0
      
        -- Expectations
        expectedResult = Matrix4
          2.0 0.0 0.0 1.0
          0.0 2.0 0.0 2.0
          0.0 0.0 2.0 3.0
          0.0 0.0 0.0 1.0
        
        -- Test
        result = scale multiplier matrix
      result `shouldEqual` expectedResult
