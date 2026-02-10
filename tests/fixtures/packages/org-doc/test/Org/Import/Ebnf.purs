module Test.Org.Import.Ebnf where

import Prelude

import Effect.Class (liftEffect, class MonadEffect)
import Control.Monad.Error.Class (class MonadThrow)

import Data.Text.Doc as D
import Data.Text.Format.Org.Render (defaultRO, RenderOptions, layoutWith) as R
import Data.Either (Either(..))

import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile)

import Test.Spec (Spec, describe, it, pending)
import Test.Spec.Assertions (shouldEqual, fail)

import Test.Utils as U

import Test.Org.Samples (samples)

import Yoga.JSON (readJSON, E)
import Data.Text.Format.Org.Parse.Ebnf (FromEbnf(..))


spec :: Spec Unit
spec = do

  describe "import using EBNF" $ do

    U.helper
        { title : const _.friendly
        , spec : \{ slug, file } -> qtest slug R.defaultRO
        }
        $ samples


renderOptions :: D.Options
renderOptions = { break : D.All, indent : D.Spaces 1 }


qtest
    :: forall (m ∷ Type -> Type)
     . Bind m => MonadEffect m => MonadThrow _ m
    => String -> R.RenderOptions -> m Unit
qtest fileSlug ro  = do
    ebnfJson <- liftEffect $ readTextFile UTF8 ("./test/examples/org-test/" <> fileSlug <> ".ebnf.json")
    let eOrgFile = (readJSON ebnfJson :: E FromEbnf)
    case eOrgFile of
        Left errors ->
            fail "Parse failed"
        Right (FromEbnf orgFile)-> do
            orgTestText <- liftEffect $ readTextFile UTF8 ("./test/examples/org-test/" <> fileSlug <> ".org")
            (D.render renderOptions $ R.layoutWith ro orgFile)
                `U.shouldEqual` orgTestText -- ``Diff.diffStackCompare` || `shouldEqual` || `Diff.diffCompare`
