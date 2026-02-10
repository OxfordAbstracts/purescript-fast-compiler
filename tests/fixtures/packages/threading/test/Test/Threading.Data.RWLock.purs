module Test.Threading.Data.RWLock where

import Prelude

import Control.Monad.Error.Class (liftMaybe)
import Data.Maybe (isNothing)
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (for_)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Console as Console
import Effect.Exception (error)
import Effect.Ref as Ref
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (expectError, shouldEqual)
import Threading.Data.RWLock as RWLock

spec :: Spec Unit
spec =
  describe "Threading.Data.RWLock" do
    describe "rwLock" do
      it "creates" $ liftEffect $ void $ RWLock.rwLock 0
    describe "read" do
      it "reads the value" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockRead m
        v <- RWLock.read g
        v `shouldEqual` 0
      it "throws if released" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockRead m
        RWLock.release g
        expectError $ RWLock.read g
    describe "write" do
      it "writes the value" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        liftEffect $ RWLock.write g 1
        v <- RWLock.read g
        v `shouldEqual` 1
      it "throws if released" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        RWLock.release g
        expectError $ liftEffect $ RWLock.write g 1
    describe "get" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        val <- RWLock.get m
        val `shouldEqual` 0
      it "blocks until unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        getFiber <- Aff.forkAff $ RWLock.get m
        liftEffect $ RWLock.write g 1
        RWLock.release g
        read <- Aff.joinFiber getFiber
        read `shouldEqual` 1
    describe "put" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        RWLock.put m 1
        val <- RWLock.get m
        val `shouldEqual` 1
      it "blocks until unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        getFiber <- Aff.forkAff $ RWLock.put m 2
        liftEffect $ RWLock.write g 1
        RWLock.release g
        Aff.joinFiber getFiber
        val <- RWLock.get m
        val `shouldEqual` 2
    describe "modify" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        val <- RWLock.modify m (_ + 1)
        val `shouldEqual` 1
      it "blocks until unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        getFiber <- Aff.forkAff $ RWLock.modify m (_ * 10)
        liftEffect $ RWLock.write g 1
        RWLock.release g
        val <- Aff.joinFiber getFiber
        val `shouldEqual` 10
    describe "lockRead" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        void $ RWLock.lockRead m
      it "blocks when write locked" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        finished <- liftEffect $ Ref.new false
        fiber <- Aff.forkAff do
          void $ RWLock.lockRead m
          void $ liftEffect $ Ref.write true finished
        Aff.delay $ Milliseconds 5.0
        f1 <- liftEffect $ Ref.read finished
        f1 `shouldEqual` false
        RWLock.release g
        Aff.joinFiber fiber
        f2 <- liftEffect $ Ref.read finished
        f2 `shouldEqual` true
      it "does not block when read locked" do
        m <- liftEffect $ RWLock.rwLock 0
        void $ Aff.forkAff $ void $ RWLock.lockRead m
        void $ Aff.forkAff $ void $ RWLock.lockRead m
        void $ RWLock.lockRead m
        n <- RWLock.get m
        n `shouldEqual` 0
      it "blocks when write locked" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        finished <- liftEffect $ Ref.new false
        fiber <- Aff.forkAff do
          g' <- RWLock.lockRead m
          liftEffect $ Ref.write true finished
          RWLock.read g'
        liftEffect $ RWLock.write g 1
        f <- liftEffect $ Ref.read finished
        f `shouldEqual` false
        RWLock.release g
        n <- Aff.joinFiber fiber
        n `shouldEqual` 1
    describe "lockWrite" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        void $ RWLock.lockWrite m
      it "blocks when write locked" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        finished <- liftEffect $ Ref.new false
        fiber <- Aff.forkAff do
          void $ RWLock.lockWrite m
          void $ liftEffect $ Ref.write true finished
        Aff.delay $ Milliseconds 5.0
        f1 <- liftEffect $ Ref.read finished
        f1 `shouldEqual` false
        RWLock.release g
        Aff.joinFiber fiber
        f2 <- liftEffect $ Ref.read finished
        f2 `shouldEqual` true
      it "blocks when read locked" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockRead m
        finished <- liftEffect $ Ref.new false
        fiber <- Aff.forkAff do
          void $ RWLock.lockWrite m
          void $ liftEffect $ Ref.write true finished
        Aff.delay $ Milliseconds 5.0
        f1 <- liftEffect $ Ref.read finished
        f1 `shouldEqual` false
        RWLock.release g
        Aff.joinFiber fiber
        f2 <- liftEffect $ Ref.read finished
        f2 `shouldEqual` true
      it "locks are acquired in the order they were requested" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- RWLock.lockWrite m
        a <- Aff.forkAff $ RWLock.modify_ m (_ + 1) -- 1
        b <- Aff.forkAff $ RWLock.modify_ m (_ * 10) -- 10
        c <- Aff.forkAff $ RWLock.modify_ m (_ + 10) -- 20
        d <- Aff.forkAff $ RWLock.modify_ m (_ * 10) -- 200
        RWLock.release g
        for_ [ a, b, c, d ] Aff.joinFiber
        n <- RWLock.get m
        n `shouldEqual` 200
    describe "tryLockWrite" do
      it "returns Just when unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        void $ liftMaybe (error $ "RWLock.tryLockWrite returned Nothing on new mutex") =<< RWLock.tryLockWrite m
      it "returns Nothing when locked" do
        m <- liftEffect $ RWLock.rwLock 0
        _ <- liftMaybe (error $ "RWLock.tryLockWrite returned Nothing on new mutex") =<< RWLock.tryLockWrite m
        g <- RWLock.tryLockWrite m
        isNothing g `shouldEqual` true
      it "returns Just after release" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- liftMaybe (error $ "RWLock.tryLockWrite returned Nothing on new mutex") =<< RWLock.tryLockWrite m
        RWLock.release g
        void $ liftMaybe (error $ "RWLock.tryLockWrite returned Nothing after lock released") =<< RWLock.tryLockWrite m
    describe "locked" do
      it "Unlocked" do
        m <- liftEffect $ RWLock.rwLock 0
        l <- liftEffect $ RWLock.locked m
        l `shouldEqual` RWLock.Unlocked
      it "LockedWriting" do
        m <- liftEffect $ RWLock.rwLock 0
        _ <- liftMaybe (error $ "RWLock.tryLockWrite returned Nothing on new mutex") =<< RWLock.tryLockWrite m
        l <- liftEffect $ RWLock.locked m
        l `shouldEqual` RWLock.LockedWriting
      it "LockedReading" do
        m <- liftEffect $ RWLock.rwLock 0
        _ <- liftMaybe (error $ "RWLock.tryLockRead returned Nothing on new mutex") =<< RWLock.tryLockRead m
        l <- liftEffect $ RWLock.locked m
        l `shouldEqual` RWLock.LockedReading
      it "Unlocked after lock released" do
        m <- liftEffect $ RWLock.rwLock 0
        g <- liftMaybe (error $ "RWLock.tryLockWrite returned Nothing on new mutex") =<< RWLock.tryLockWrite m
        RWLock.release g
        l' <- liftEffect $ RWLock.locked m
        l' `shouldEqual` RWLock.Unlocked
