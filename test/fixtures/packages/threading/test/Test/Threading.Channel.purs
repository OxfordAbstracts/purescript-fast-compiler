module Test.Threading.Channel where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Array as Array
import Data.Maybe (Maybe(..), isNothing, maybe)
import Data.Traversable (traverse)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Console as Console
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (expectError, shouldEqual)
import Threading.Channel as Channel

spec :: Spec Unit
spec =
  describe "Threading.Channel" do
    describe "channel" do
      it "creates" $ liftEffect $ void $ Channel.channel
    describe "receiver" do
      it "creates" do
        c <- liftEffect $ Channel.channel
        void $ Channel.receiver c
    describe "Sender" do
      describe "send" do
        it "does nothing when no receivers" do
          c <- liftEffect $ Channel.channel
          s <- liftEffect $ Channel.sender c
          Channel.send s 0
        it "broadcasts to multiple receivers" do
          c <- liftEffect $ Channel.channel
          s <- liftEffect $ Channel.sender c
          ra <- Channel.receiver c
          rb <- Channel.receiver c
          fiber <- Aff.forkAff $ traverse Channel.recv [ ra, rb ]
          Channel.send s 100
          as <- Aff.joinFiber fiber
          as `shouldEqual` [ 100, 100 ]
    describe "Receiver" do
      describe "recv" do
        it "throws if multiple fibers blocking" do
          c <- liftEffect $ Channel.channel
          r <- Channel.receiver c
          void $ Aff.forkAff $ Channel.recv r
          expectError $ Channel.recv r
        it "recv resolves with messages in the order they were sent" do
          c <- liftEffect $ Channel.channel
          s <- liftEffect $ Channel.sender c
          r <- Channel.receiver c
          Channel.send s $ Just 1
          Channel.send s $ Just 2
          Channel.send s $ Just 3
          Channel.send s $ Just 4
          fiber <- Aff.forkAff $ flip tailRecM [] \as -> maybe (Done as) (Loop <<< Array.snoc as) <$> Channel.recv r
          Channel.send s $ Just 5
          Channel.send s Nothing
          as <- Aff.joinFiber fiber
          as `shouldEqual` [ 1, 2, 3, 4, 5 ]
        it "blocks until a message is sent" do
          c <- liftEffect $ Channel.channel
          s <- liftEffect $ Channel.sender c
          r <- Channel.receiver c
          fiber <- Aff.forkAff $ Channel.recv r
          Channel.send s 10
          a <- Aff.joinFiber fiber
          a `shouldEqual` 10
        it "immediately resolves if a message buffered" do
          c <- liftEffect $ Channel.channel
          s <- liftEffect $ Channel.sender c
          r <- Channel.receiver c
          Channel.send s 10
          a <- Channel.recv r
          a `shouldEqual` 10
      describe "tryRecv" do
        it "returns Nothing when no data has been sent" do
          c <- liftEffect $ Channel.channel
          r <- Channel.receiver c
          ma <- Channel.tryRecv r
          isNothing ma `shouldEqual` true
        it "returns Just when a message has been buffered" do
          c <- liftEffect $ Channel.channel
          s <- liftEffect $ Channel.sender c
          r <- Channel.receiver c
          Channel.send s 10
          ma <- Channel.tryRecv r
          ma `shouldEqual` (Just 10)
    describe "sender" do
      it "creates" do
        c <- liftEffect $ Channel.channel
        void $ liftEffect $ Channel.sender c
