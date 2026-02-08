module Test.Threading.Barrier where

import Prelude

import Data.Newtype (wrap)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Threading.Barrier as Barrier

spec :: Spec Unit
spec =
  describe "Threading.Barrier" do
    it "creates" do
      void $ liftEffect $ Barrier.barrier 1
    it "barrer 1 >>= wait immediately resolves" do
      b <- liftEffect $ Barrier.barrier 1
      Barrier.wait b
    it "barrer only resolves when all 3 threads wait" do
      barrier <- liftEffect $ Barrier.barrier 3

      aDone <- liftEffect $ Ref.new false
      bDone <- liftEffect $ Ref.new false
      a <- Aff.forkAff do
        Barrier.wait barrier
        liftEffect $ Ref.write true aDone
      b <- Aff.forkAff do
        Barrier.wait barrier
        liftEffect $ Ref.write true bDone

      Aff.delay $ wrap 10.0
      liftEffect (Ref.read aDone) >>= shouldEqual false
      liftEffect (Ref.read bDone) >>= shouldEqual false

      Barrier.wait barrier
      Aff.joinFiber a
      Aff.joinFiber b
      liftEffect (Ref.read aDone) >>= shouldEqual true
      liftEffect (Ref.read bDone) >>= shouldEqual true
