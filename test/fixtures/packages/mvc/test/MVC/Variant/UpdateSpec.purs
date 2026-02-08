module Test.MVC.Variant.UpdateSpec where

import Prelude

import Data.Variant (Variant)
import Data.Variant as V
import MVC.Variant.Types (VariantMsg(..), VariantState(..))
import MVC.Variant.Update (matchCase, matchCaseRL, updateVariantRL, updateVariant)
import Prim.RowList as RL
import Test.MVC.TestTypes (M1(..), M2(..), M3, S1(..), S2(..), S3(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Function (type (#), type ($))
import Type.Proxy (Proxy(..))

testUpdate1 :: VariantState (case1 :: S1, case2 :: S2, case3 :: S3)
testUpdate1 = updateVariant
  { case1: S1
  , case2: S2
  , case3: S3
  }
  { case1: \(_ :: M1) (_ :: S1) -> S1
  , case2: \(_ :: M2) (_ :: S2) -> S2
  , case3: \(_ :: M3) (_ :: S3) -> S3
  }
  (ChildCaseMsg (V.inj (Proxy :: Proxy "case1") M1))
  (VariantState (V.inj (Proxy :: Proxy "case1") S1))

testUpdate2 :: VariantState (case1 :: S1, case2 :: S2, case3 :: S3)
testUpdate2 = updateVariant
  { case1: S1
  , case2: S2
  , case3: S3
  }
  { case1: \(_ :: M1) (_ :: S1) -> S1
  , case2: \(_ :: M2) (_ :: S2) -> S2
  , case3: \(_ :: M3) (_ :: S3) -> S3
  }
  (ChangeCase (V.inj (Proxy :: Proxy "case1") unit))
  (VariantState (V.inj (Proxy :: Proxy "case1") S1))

testUpdateRL :: Variant (case1 :: S1, case2 :: S2, case3 :: S3)
testUpdateRL = updateVariantRL
  ( Proxy
      :: _ $ RL.Nil
           # RL.Cons "case1" Unit
           # RL.Cons "case2" Unit
           # RL.Cons "case3" Unit
  )
  { case1: \(_ :: M1) (_ :: S1) -> S1
  , case2: \(_ :: M2) (_ :: S2) -> S2
  , case3: \(_ :: M3) (_ :: S3) -> S3
  }
  (V.inj (Proxy :: Proxy "case1") M1)
  (V.inj (Proxy :: Proxy "case1") S1)

testMatchCase :: Variant (case1 :: S1, case2 :: S2, case3 :: S3)
testMatchCase = matchCase
  { case1: S1
  , case2: S2
  , case3: S3
  }
  (V.inj (Proxy :: Proxy "case2") unit)

testMatchCaseRL :: Variant (case1 :: S1, case2 :: S2, case3 :: S3)
testMatchCaseRL = matchCaseRL
  ( Proxy
      :: _ $ RL.Nil
           # RL.Cons "case3" Unit
           # RL.Cons "case2" Unit
           # RL.Cons "case1" Unit
  )
  { case1: S1
  , case2: S2
  , case3: S3
  }
  (V.inj (Proxy :: Proxy "case2") unit)

spec :: Spec Unit
spec =
  describe "MVC.Variant.Update" do
    describe "updateVariant" do
      it "should change case correctly" do
        let
          update = updateVariant
            { case1: S1
            , case2: S2
            , case3: S3
            }
            { case1: \_ state -> state
            , case2: \_ state -> state
            , case3: \_ state -> state
            }

        update
          (ChangeCase (V.inj (Proxy :: Proxy "case2") unit))
          (VariantState (V.inj (Proxy :: Proxy "case1") S1))
          `shouldEqual`
            (VariantState $ V.inj (Proxy :: Proxy "case2") S2)

        update
          (ChangeCase (V.inj (Proxy :: Proxy "case1") unit))
          (VariantState (V.inj (Proxy :: Proxy "case1") S1))
          `shouldEqual`
            (VariantState $ V.inj (Proxy :: Proxy "case1") S1)

      it "should update child case correctly" do
        let
          update = updateVariant
            { case1: S1
            , case2: S2
            , case3: S3
            }
            { case1: \_ state -> state
            , case2: \msg state -> case msg, state of
                M2, S2' -> S2''
                _, _ -> state
            , case3: \_ state -> state
            }

        update
          (ChildCaseMsg (V.inj (Proxy :: Proxy "case2") M2))
          (VariantState (V.inj (Proxy :: Proxy "case2") S2'))
          `shouldEqual`
            (VariantState $ V.inj (Proxy :: Proxy "case2") S2'')

        update
          (ChildCaseMsg (V.inj (Proxy :: Proxy "case2") M2))
          (VariantState (V.inj (Proxy :: Proxy "case1") S1'))
          `shouldEqual`
            (VariantState $ V.inj (Proxy :: Proxy "case1") S1')

