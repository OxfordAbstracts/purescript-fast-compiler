module Test.Org.Export.Json where

import Prelude
import Foreign as F

import Effect.Class (liftEffect, class MonadEffect)
import Effect.Console as Console
import Control.Monad.Error.Class (class MonadThrow)

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Traversable (traverse_)
-- import Data.Text.Doc as D

import Data.Text.Doc as D
import Data.Text.Format.Org.Types (OrgFile, Check(..))
import Data.Text.Format.Org.Construct as Org
import Data.Text.Format.Org.Render as R

import Yoga.JSON (E, read_, read, readJSON, write, writeJSON)

import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile)

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual, shouldNotEqual)

import Test.Utils as U

import Test.Org.Samples (samples)


spec :: Spec Unit
spec = do

  describe "export to JSON" $ do

    it "properly encodes variants" $ do
        (writeJSON Check) `shouldNotEqual` (writeJSON Uncheck)
        (writeJSON Check) `shouldNotEqual` (writeJSON Halfcheck)
        (writeJSON Uncheck) `shouldNotEqual` (writeJSON Halfcheck)
        (read_ $ write Check) `shouldEqual` (Just Check)
        (read_ $ write Uncheck) `shouldEqual` (Just Uncheck)
        (read_ $ write Halfcheck) `shouldEqual` (Just Halfcheck)

    {-
    it "works with the empty .org files" $ do
        (read_ $ write Org.empty) `shouldEqual` (Just Org.empty)
    -}

    it "works with the empty JSON" $ do
        emptySample <- liftEffect $ readTextFile UTF8 "./test/examples/org-empty.json"
        (writeJSON Org.empty) `shouldEqual` emptySample

    describe "samples" $
        U.helper
            { title : const _.friendly
            , spec : \{ file } -> liftEffect file >>= qjsontest
            }
            $ samples


renderOptions :: D.Options
renderOptions = { break : D.All, indent : D.Spaces 1 }


qjsontest
    :: forall (m ∷ Type -> Type)
     . Bind m => MonadEffect m => MonadThrow _ m
    => OrgFile -> m Unit
qjsontest orgFile = do
    let orgFileJson = writeJSON orgFile
    let eFromJsonTxt = (readJSON orgFileJson :: E OrgFile)
    -- liftEffect $ Console.log orgFileJson
    let eFromJsonF = read $ write orgFile
    case eFromJsonF of
        Right orgFileFromJsonF ->
            (D.render renderOptions $ R.layout orgFile)
                `U.shouldEqual` (D.render renderOptions $ R.layout orgFileFromJsonF)
        Left errors ->
            traverse_ (F.renderForeignError >>> fail) errors
    case eFromJsonTxt of
        Right orgFileFromJsonTxt -> do
            writeJSON orgFileFromJsonTxt `U.shouldEqual` orgFileJson
            (D.render renderOptions $ R.layout orgFile)
                `U.shouldEqual` (D.render renderOptions $ R.layout orgFileFromJsonTxt)
        Left errors ->
            traverse_ (F.renderForeignError >>> fail) errors
