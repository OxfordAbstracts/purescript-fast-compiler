module Test.MVC.Variant.ViewSpec where

import Prelude

import Data.Maybe (Maybe)
import Data.Newtype (un)
import Data.Variant (Variant)
import Data.Variant as V
import MVC.Variant.Types (CaseKey(..), VariantMsg(..), VariantState(..))
import MVC.Variant.View (caseKeyToVariantRL, getKeys, viewVariantRL, viewVariant)
import Prim.RowList as RL
import Test.MVC.TestTypes (HTML(..), M1, M2, M3, S1(..), S2(..), S3)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Function (type (#), type ($))
import Type.Proxy (Proxy(..))
import Chameleon as VD
import Chameleon.Impl.TestHtml (TestHtml)

testView
  :: HTML
       ( VariantMsg
           ( case1 :: Unit
           , case2 :: Unit
           , case3 :: Unit
           )
           ( case1 :: M1
           , case2 :: M2
           , case3 :: M3
           )
       )
testView = viewVariant
  { view: \_ -> HTML
  }
  { case1: \(_ :: S1) -> HTML :: _ M1
  , case2: \(_ :: S2) -> HTML :: _ M2
  , case3: \(_ :: S3) -> HTML :: _ M3
  }
  (VariantState $ V.inj (Proxy :: Proxy "case1") S1)

testCaseKeyToVariantRL
  :: Maybe
       ( Variant
           ( case1 :: Unit
           , case2 :: Unit
           , case3 :: Unit
           )
       )
testCaseKeyToVariantRL = caseKeyToVariantRL
  ( Proxy
      :: _ $ RL.Nil
           # RL.Cons "case3" Unit
           # RL.Cons "case2" Unit
           # RL.Cons "case1" Unit
  )
  (CaseKey "case2")

testViewRL
  :: HTML
       ( Variant
           ( case1 :: M1
           , case2 :: M2
           , case3 :: M3
           )
       )
testViewRL = viewVariantRL
  ( Proxy
      :: _ $ RL.Nil
           # RL.Cons "case1" Unit
           # RL.Cons "case2" Unit
           # RL.Cons "case3" Unit
  )
  { case1: \(_ :: S1) -> HTML :: _ M1
  , case2: \(_ :: S2) -> HTML :: _ M2
  , case3: \(_ :: S3) -> HTML :: _ M3
  }
  (V.inj (Proxy :: Proxy "case1") S1)

testGetKeys :: Array String
testGetKeys = getKeys
  ( Proxy
      :: _
           ( RL.Nil
               # RL.Cons "c" Unit
               # RL.Cons "b" Unit
               # RL.Cons "a" Unit
           )
  )

type Msg =
  ( VariantMsg
      ( case1 :: Unit
      , case2 :: Unit
      , case3 :: Unit
      )
      ( case1 :: M1
      , case2 :: M2
      , case3 :: M3
      )
  )

spec :: Spec Unit
spec =
  describe "MVC.Variant.View" do
    describe "viewVariant" do
      it "should render views" do
        let
          actual :: TestHtml Msg
          actual = viewVariant
            { view: \{ viewCase, mkMsg, caseKey, caseKeys } ->
                VD.div_
                  [ VD.select
                      [ VD.onChange (CaseKey >>> mkMsg)
                      , VD.value $ un CaseKey caseKey
                      ]
                      ( caseKeys # map \(CaseKey s) ->
                          VD.option [ VD.value s ] [ VD.text s ]
                      )
                  , VD.hr_
                  , viewCase
                  ]
            }
            { case1: \(state :: S1) -> VD.text $ show state
            , case2: \(state :: S2) -> VD.text $ show state
            , case3: \(state :: S3) -> VD.text $ show state
            }
            (VariantState $ V.inj (Proxy :: Proxy "case2") S2)

          expected :: TestHtml Msg
          expected =
            VD.div_
              [ VD.select
                  [ VD.onChange (\_ -> ChangeCase $ V.inj (Proxy :: _ "case1") unit)
                  , VD.value "case2"
                  ]
                  [ VD.option [ VD.value "case1" ] [ VD.text "case1" ]
                  , VD.option [ VD.value "case2" ] [ VD.text "case2" ]
                  , VD.option [ VD.value "case3" ] [ VD.text "case3" ]
                  ]
              , VD.hr_
              , VD.text "S2"
              ]

        actual `shouldEqual` expected
