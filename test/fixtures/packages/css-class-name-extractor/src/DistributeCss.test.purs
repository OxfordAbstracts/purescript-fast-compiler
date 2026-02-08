module Test.CssClassNameExtractor.DistributeCss where

import Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.RWS (modify_)
import Control.Monad.Reader (class MonadAsk, ReaderT, runReaderT)
import Control.Monad.State (class MonadState, StateT, get, runStateT)
import CssClassNameExtractor.Data.Output (FileBody(..), Namespace(..), coerceFileBody)
import CssClassNameExtractor.DistributeCss (distributeCss)
import CssClassNameExtractor.FS (class MonadFS)
import Data.Either (isLeft)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, attempt, error)
import Effect.Class (class MonadEffect, liftEffect)
import Node.Path (FilePath)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

type FileSystem = Map FilePath FileBody

newtype TestM a = TestM (StateT FileSystem (ReaderT {} Aff) a)

derive newtype instance functorTestM :: Functor TestM
derive newtype instance applyTestM :: Apply TestM
derive newtype instance applicativeTestM :: Applicative TestM
derive newtype instance bindTestM :: Bind TestM
derive newtype instance monadTestM :: Monad TestM
derive newtype instance monadEffectTestM :: MonadEffect TestM
derive newtype instance monadAskTestM :: MonadAsk {} TestM
derive newtype instance monadStateTestM :: MonadState FileSystem TestM

instance monadFSTestM :: MonadFS TestM where
  readFile path = do
    fs <- get
    case Map.lookup path fs of
      Just content -> pure (coerceFileBody content)
      Nothing -> liftEffect $ throwError $ error $ "File not found: " <> path

  writeFile path content = do
    modify_ $ Map.insert path content

  isExists _ = pure true

runTest :: forall a. FileSystem -> TestM a -> Aff (Tuple a FileSystem)
runTest init (TestM m) =
  runReaderT (runStateT m init)  {}

initialFS :: FileSystem
initialFS = Map.empty

spec :: Spec Unit
spec = do
  describe "distributeCss" do
    describe "when File not found" do
      it "should throw File not found" do
        result <- attempt $ runTest initialFS (distributeCss "./notfound/foo.css" (Namespace "Foo"))
        isLeft result `shouldEqual` true

    describe "when File found" do
      it "should distribute to output directory" do
        let inputFS = Map.insert "./components/styles.module.css" (FileBody ".foo { display: flex; }") initialFS
        result <- runTest inputFS (distributeCss "./components/styles.module.css" (Namespace "Foo"))
        let expectedContent = FileBody """.foo { display: flex; }"""
        case result of
          Tuple _ finalFS -> do
            let generatedFile = Map.lookup "output/Foo/styles.module.css" finalFS
            generatedFile `shouldEqual` (Just expectedContent)
