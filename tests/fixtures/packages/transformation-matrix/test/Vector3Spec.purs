module Test.Vector3Spec where

import Prelude hiding (add)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Data.Number (sqrt)
import Data.Either (Either(..))
import Data.TransformationMatrix.Vector3 
  ( Vector3(..)
  , lengthSquared
  , length
  , subtract
  , add
  , dotProduct
  , crossProduct
  , divideByScalar
  , multiplyByScalar
  , normalize
  , distanceBetweenSquared )

vector3Spec :: Spec Unit
vector3Spec = do
  describe "Vector3Spec" do
    it "should calculate the length squared of a Vector3" do
      let
        -- Setup
        vector3 = Vector3 1.0 3.0 2.0
      
        -- Expectations
        expectedResult = 1.0 + 9.0 + 4.0

        -- Test
        result = lengthSquared vector3
      result `shouldEqual` expectedResult

    it "should calculate the length of a Vector3" do
      let
        -- Setup
        vector3 = Vector3 1.0 3.0 2.0
      
        -- Expectations
        expectedResult = sqrt 14.0

        -- Tests
        result = length vector3
      result `shouldEqual` expectedResult

    it "should subtract Vector3s" do
      let
        -- Setup
        vector3_1 = Vector3 1.0 3.0 2.0
        vector3_2 = Vector3 2.0 1.0 3.0
      
        -- Expectations
        expectedResult = Vector3 (-1.0) 2.0 (-1.0)

        -- Test
        result = subtract vector3_1 vector3_2
      result `shouldEqual` expectedResult

    it "should add Vector3s" do
      let
        -- Setup
        vector3_1 = Vector3 1.0 3.0 2.0
        vector3_2 = Vector3 2.0 1.0 3.0
      
        -- Expectations
        expectedResult = Vector3 3.0 4.0 5.0

        -- Test
        result = add vector3_1 vector3_2
      result `shouldEqual` expectedResult
    
    it "should calculate the dot product of two Vector3s" do
      let
        -- Setup
        vector3_1 = Vector3 1.0 3.0 2.0
        vector3_2 = Vector3 2.0 1.0 3.0
      
        -- Expectations
        expectedResult = 2.0 + 3.0 + 6.0

        -- Test
        result = dotProduct vector3_1 vector3_2
      result `shouldEqual` expectedResult
    
    it "should calculate the cross product of two Vector3s" do
      let
        -- Setup
        vector3_1 = Vector3 1.0 3.0 2.0
        vector3_2 = Vector3 2.0 1.0 3.0
      
        -- Expectations
        expectedResult = Vector3 
          (3.0 * 3.0 - 2.0 * 1.0) 
          (2.0 * 2.0 - 1.0 * 3.0) 
          (1.0 * 1.0 - 3.0 * 2.0)

        -- Test
        result = crossProduct vector3_1 vector3_2
      result `shouldEqual` expectedResult

    it "should divide by scalar" do
      let
        -- Setup
        vector3 = Vector3 1.0 3.0 2.0
      
        -- Expectations
        expectedResult = Right $ Vector3 0.5 1.5 1.0

        -- Test
        result = divideByScalar 2.0 vector3
      result `shouldEqual` expectedResult

    it "should multiply by scalar" do
      let
        -- Setup
        vector3 = Vector3 1.0 3.0 2.0
      
        -- Expectations
        expectedResult = Vector3 2.0 6.0 4.0

        -- Test
        result = multiplyByScalar 2.0 vector3
      result `shouldEqual` expectedResult

    it "should normalize a Vector3" do
      let
        -- Setup
        vector3 = Vector3 1.0 2.0 4.0
      
        -- Expectations
        len = length vector3
        expectedResult = Right $ Vector3 (1.0 / len) (2.0 / len) (4.0 / len)

        -- Test
        result = normalize vector3
      result `shouldEqual` expectedResult
    
    it "should calculate the distance squared between two Vector3s" do
      let
        -- Setup
        vector3_1 = Vector3 1.0 3.0 2.0
        vector3_2 = Vector3 2.0 1.0 3.0
      
        -- Expectations
        expectedResult = 1.0 + 4.0 + 1.0

        -- Test
        result = distanceBetweenSquared vector3_1 vector3_2
      result `shouldEqual` expectedResult
