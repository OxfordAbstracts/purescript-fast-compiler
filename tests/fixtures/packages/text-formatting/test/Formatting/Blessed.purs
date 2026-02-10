module Test.Formatting.Blessed where

import Prelude

import Data.Tuple.Nested (type (/\), (/\))
import Data.Text.Output.Blessed (multiLine) as T
import Data.Text.Format as F
-- import Data.Text.Doc as D

import Test.Spec (Spec, describe)

import Test.Formatting.Utils (helper)


blessedSamples :: Array (F.Tag /\ String)
blessedSamples =
    [ F.s "foo" /\ "foo"
    , F.bolds "test" /\ "{bold}test{/bold}"
    ]


spec :: Spec Unit
spec = do

  describe "Formatting works properly for Blessed" $ do

    helper
        { title : \idx (_ /\ expected) -> show idx <> " : " <> expected
        , render : T.multiLine
        }
        blessedSamples
