module Test.Spec.Reporter.Xunit
       ( xunitReporter
       , defaultOptions
       ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.XML as XML
import Data.XML.PrettyPrint (print)
import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Exception (message)
import Node.Encoding (Encoding(UTF8))
import Node.FS.Sync (writeTextFile, exists, unlink)
import Node.Path (FilePath)
import Pipes.Prelude (chain)
import Test.Spec as S
import Test.Spec.Result as R
import Test.Spec.Runner (Reporter)
import Test.Spec.Runner.Event as Event

encodeResult :: R.Result -> Array XML.Node
encodeResult (R.Success _speed _ms) = []
encodeResult (R.Failure err) =
  [XML.Element
    "error"
    [XML.Attr "message" (message err)]
    [XML.Text (show err)]]

encodeGroup :: S.Tree String Void R.Result -> XML.Node
encodeGroup (S.Node (Left name) groups) =
  XML.Element "testsuite" [XML.Attr "name" name] $ map encodeGroup groups
encodeGroup (S.Node (Right _) groups) =
  XML.Element "testsuite" [] $ map encodeGroup groups
encodeGroup (S.Leaf name (Just result)) =
  XML.Element "testcase" [XML.Attr "name" name] (encodeResult result)
encodeGroup (S.Leaf name Nothing) =
  XML.Element "testcase" [XML.Attr "name" name] [XML.Element "skipped" [] []]

encodeSuite :: Array (S.Tree String Void R.Result) -> XML.Document
encodeSuite groups = XML.Document "1.0" "UTF-8" $ XML.Element "testsuite" [] $ map encodeGroup groups

removeIfExists :: FilePath -> Effect Unit
removeIfExists path = do
  e <- exists path
  when e $ unlink path

type XunitReporterOptions = { outputPath :: FilePath
                            , indentation :: Int
                            }

defaultOptions :: XunitReporterOptions
defaultOptions = { indentation: 2, outputPath: "output/test.xml" }


-- | Outputs an XML file at a specified path that can be consumed by Xunit
-- | readers, e.g. the Jenkins plugin.
xunitReporter :: XunitReporterOptions -> Reporter
xunitReporter options = chain handleEvent
  where

    handleEvent = case _ of
      Event.End results -> void $ liftEffect $ summarize results
      _                 -> pure unit

    summarize groups = do
      let xml = encodeSuite groups
      removeIfExists options.outputPath
      writeTextFile UTF8 options.outputPath (print options.indentation xml)
