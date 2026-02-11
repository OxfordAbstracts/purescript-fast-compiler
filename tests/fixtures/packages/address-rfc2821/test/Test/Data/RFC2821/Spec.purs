module Test.Data.RFC2821.Spec where

import Data.Either (Either(..))
import Data.RFC2821 as RFC2821
-- import Debug (spy)
import Effect.Exception as Exception
import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)


spec :: Spec Unit
spec =
  describe "RFC2821" do
    it "works for simple email" do
      let eAddress = RFC2821.makeAddress "admin@localhost.localdomain"
      case eAddress of
        Left e -> fail $ "Address parsing returned an error: " <> Exception.message e
        Right address -> do
          RFC2821.original address `shouldEqual` "admin@localhost.localdomain"
          RFC2821.host address `shouldEqual` "localhost.localdomain"
          RFC2821.user address `shouldEqual` "admin"

    it "works for incorrect email" do
      let eAddress = RFC2821.makeAddress "admin"
      case eAddress of
        Left _e -> pure unit
        Right _a -> fail $ "It is incorrect for address to parse here!"
    
    it "shouldn't parse email with symbols surrounding it" $ do
      let eAddress = RFC2821.makeAddress "'admin@localhost.localdomain'"
      case eAddress of
        Left _e -> pure unit
        Right _a -> fail $ "It is incorrect for address to parse here!"

    it "parses email with <>" $ do
      let eAddress = RFC2821.makeAddress "<admin@localhost.localdomain>"
      case eAddress of
        Left e -> fail $ "Address parsing returned an error: " <> Exception.message e
        Right _a -> pure unit

    it "reformatting address as string works" $ do
      let eAddress = RFC2821.makeAddress "<admin@localhost.localdomain>"
      case eAddress of
        Left e -> fail $ "Address parsing returned an error: " <> Exception.message e
        Right address -> do
          RFC2821.address address `shouldEqual` "admin@localhost.localdomain"

    it "reformatting address as envelope works" $ do
      let eAddress = RFC2821.makeAddress "admin@localhost.localdomain"
      case eAddress of
        Left e -> fail $ "Address parsing returned an error: " <> Exception.message e
        Right address -> do
          RFC2821.toString address `shouldEqual` "<admin@localhost.localdomain>"
