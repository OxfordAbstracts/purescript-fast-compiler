module Test.Threading.Data.Mutex where

import Prelude

import Control.Monad.Error.Class (liftEither, liftMaybe)
import Control.Parallel (parOneOf)
import Data.Either (Either(..))
import Data.Maybe (isNothing)
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (for_)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Exception (error)
import Effect.Ref as Ref
import Test.Spec (Spec, describe, it, pending')
import Test.Spec.Assertions (expectError, shouldEqual)
import Threading.Data.Mutex as Mutex

spec :: Spec Unit
spec =
  describe "Threading.Data.Mutex" do
    describe "mutex" do
      it "creates" $ liftEffect $ void $ Mutex.mutex 0
    describe "read" do
      it "reads the value" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        v <- liftEffect $ Mutex.read g
        v `shouldEqual` 0
      it "throws if released" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        liftEffect $ Mutex.release g
        expectError $ liftEffect $ Mutex.read g
    describe "write" do
      it "writes the value" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        liftEffect $ Mutex.write g 1
        v <- liftEffect $ Mutex.read g
        v `shouldEqual` 1
      it "throws if released" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        liftEffect $ Mutex.release g
        expectError $ liftEffect $ Mutex.write g 1
    describe "get" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        val <- Mutex.get m
        val `shouldEqual` 0
      it "blocks until unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        getFiber <- Aff.forkAff $ Mutex.get m
        liftEffect $ Mutex.write g 1
        liftEffect $ Mutex.release g
        read <- Aff.joinFiber getFiber
        read `shouldEqual` 1
    describe "put" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        Mutex.put m 1
        val <- Mutex.get m
        val `shouldEqual` 1
      it "blocks until unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        getFiber <- Aff.forkAff $ Mutex.put m 2
        liftEffect $ Mutex.write g 1
        liftEffect $ Mutex.release g
        Aff.joinFiber getFiber
        val <- Mutex.get m
        val `shouldEqual` 2
    describe "modify" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        val <- Mutex.modify m (_ + 1)
        val `shouldEqual` 1
      it "blocks until unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        getFiber <- Aff.forkAff $ Mutex.modify m (_ * 10)
        liftEffect $ Mutex.write g 1
        liftEffect $ Mutex.release g
        val <- Aff.joinFiber getFiber
        val `shouldEqual` 10
    describe "lock" do
      it "yields immediately when unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        void $ Mutex.lock m
      it "blocks when locked" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        finished <- liftEffect $ Ref.new false
        fiber <- Aff.forkAff do
          void $ Mutex.lock m
          void $ liftEffect $ Ref.write true finished
        Aff.delay $ Milliseconds 5.0
        f1 <- liftEffect $ Ref.read finished
        f1 `shouldEqual` false
        liftEffect $ Mutex.release g
        Aff.joinFiber fiber
        f2 <- liftEffect $ Ref.read finished
        f2 `shouldEqual` true
      it "locks are acquired in the order they were requested" do
        m <- liftEffect $ Mutex.mutex 0
        g <- Mutex.lock m
        a <- Aff.forkAff $ Mutex.modify_ m (_ + 1) -- 1
        b <- Aff.forkAff $ Mutex.modify_ m (_ * 10) -- 10
        c <- Aff.forkAff $ Mutex.modify_ m (_ + 10) -- 20
        d <- Aff.forkAff $ Mutex.modify_ m (_ * 10) -- 200
        liftEffect $ Mutex.release g
        for_ [ a, b, c, d ] Aff.joinFiber
        n <- Mutex.get m
        n `shouldEqual` 200
      pending' "should be (eventually) unlocked if a fiber exits without releasing the lock" do
        m <- liftEffect $ Mutex.mutex 0
        -- Fiber acquires a lock then immediately resolves without releasing.
        --
        -- When the GC reclaims the guard object, the Mutex should notice and behave
        -- as if it was explicitly released.
        void $ Aff.forkAff $ void $ Mutex.lock m
        liftEither =<< parOneOf
          [ Aff.delay (Milliseconds 20000.0) $> Left (error "timed out waiting for GC to reclaim lock")
          , Mutex.lock m $> Right unit
          ]
    describe "tryLock" do
      it "returns Just when unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        void $ liftMaybe (error $ "Mutex.tryLock returned Nothing on new mutex") =<< liftEffect (Mutex.tryLock m)
      it "returns Nothing when locked" do
        m <- liftEffect $ Mutex.mutex 0
        _ <- liftMaybe (error $ "Mutex.tryLock returned Nothing on new mutex") =<< liftEffect (Mutex.tryLock m)
        g <- liftEffect (Mutex.tryLock m)
        isNothing g `shouldEqual` true
      it "returns Just after release" do
        m <- liftEffect $ Mutex.mutex 0
        g <- liftMaybe (error $ "Mutex.tryLock returned Nothing on new mutex") =<< liftEffect (Mutex.tryLock m)
        liftEffect $ Mutex.release g
        void $ liftMaybe (error $ "Mutex.tryLock returned Nothing after lock released") =<< liftEffect (Mutex.tryLock m)
    describe "locked" do
      it "is false when unlocked" do
        m <- liftEffect $ Mutex.mutex 0
        l <- liftEffect $ Mutex.locked m
        l `shouldEqual` false
      it "is true when locked" do
        m <- liftEffect $ Mutex.mutex 0
        _ <- liftMaybe (error $ "Mutex.tryLock returned Nothing on new mutex") =<< liftEffect (Mutex.tryLock m)
        l <- liftEffect $ Mutex.locked m
        l `shouldEqual` true
      it "is false after lock released" do
        m <- liftEffect $ Mutex.mutex 0
        g <- liftMaybe (error $ "Mutex.tryLock returned Nothing on new mutex") =<< liftEffect (Mutex.tryLock m)
        liftEffect $ Mutex.release g
        l' <- liftEffect $ Mutex.locked m
        l' `shouldEqual` false
