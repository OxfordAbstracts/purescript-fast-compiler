module Test.MVC.Record.ViewSpec where

import Prelude

import Data.Variant as V
import MVC.Record (RecordMsg(..))
import MVC.Record as ME
import Prim.RowList as RL
import Test.MVC.TestTypes (HTML(..), M1(..), M2(..), M3(..), S1(..), S2(..), S3(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Function (type (#), type ($))
import Type.Proxy (Proxy(..))
import Chameleon as VD
import Chameleon.Impl.TestHtml (TestHtml)

testView
  :: HTML
       ( ME.RecordMsg
           ( field1 :: M1
           , field2 :: M2
           , field3 :: M3
           )
       )
testView = ME.viewRecord
  { field1: \(_ :: S1) -> HTML :: _ M1
  , field2: \(_ :: S2) -> HTML :: _ M2
  , field3: \(_ :: S3) -> HTML :: _ M3
  }
  { viewEntries: \_ -> HTML
  }
  ( ME.RecordState
      { field1: S1
      , field2: S2
      , field3: S3
      }
  )

testViewRL
  :: Array
       ( ME.ViewResult HTML
           ( ME.RecordMsg
               ( field1 :: M1
               , field2 :: M2
               , field3 :: M3
               )
           )
       )
testViewRL = ME.viewRecordRL
  ( Proxy
      :: _ $ RL.Nil
           # RL.Cons "field3" Unit
           # RL.Cons "field2" Unit
           # RL.Cons "field1" Unit
  )
  { field1: \(_ :: S1) -> HTML :: _ M1
  , field2: \(_ :: S2) -> HTML :: _ M2
  , field3: \(_ :: S3) -> HTML :: _ M3
  }
  ( ME.RecordState
      { field1: S1
      , field2: S2
      , field3: S3
      }
  )

type Msg =
  ME.RecordMsg
    ( field1 :: M1
    , field2 :: M2
    , field3 :: M3
    )

spec :: Spec Unit
spec =
  describe "MVC.Record.View"
    do
      describe "viewRecord" do
        it "should render views" do
          let
            actual :: TestHtml Msg
            actual = ME.viewRecord
              { field1: \state -> VD.div [ VD.onClick M1 ] [ VD.text $ show state ]
              , field2: \state -> VD.div [ VD.onClick M2 ] [ VD.text $ show state ]
              , field3: \state -> VD.div [ VD.onClick M3 ] [ VD.text $ show state ]
              }
              { viewEntries: \xs ->
                  VD.div_
                    ( xs # map \x ->
                        VD.div_
                          [ VD.text x.key
                          , x.viewValue
                          ]
                    )
              }
              ( ME.RecordState
                  { field1: S1
                  , field2: S2
                  , field3: S3
                  }
              )

            expected :: TestHtml Msg
            expected =
              VD.div_
                [ VD.div_
                    [ VD.text "field1"
                    , VD.div [ VD.onClick $ SetField $ V.inj (Proxy :: _ "field1") M1 ] [ VD.text "S1" ]
                    ]
                , VD.div_
                    [ VD.text "field2"
                    , VD.div [ VD.onClick $ SetField $ V.inj (Proxy :: _ "field2") M2 ] [ VD.text "S2" ]
                    ]
                , VD.div_
                    [ VD.text "field3"
                    , VD.div [ VD.onClick $ SetField $ V.inj (Proxy :: _ "field3") M3 ] [ VD.text "S3" ]
                    ]
                ]

          actual `shouldEqual` expected
