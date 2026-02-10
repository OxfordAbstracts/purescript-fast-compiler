module Test.CssClassNameExtractor.Execute where

import Prelude

import CssClassNameExtractor.Data.Output (FileBody(..), Namespace(..), coerceFileBody)
import CssClassNameExtractor.Execute (execute)
import CssClassNameExtractor.FS (class MonadFS)
import CssClassNameExtractor.RIO (Env)
import Control.Monad.Except (throwError)
import Control.Monad.Reader (class MonadAsk, ReaderT, runReaderT)
import Control.Monad.State (class MonadState, StateT, get, modify_, runStateT)
import Data.Either (isLeft)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff, attempt)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Effect.Exception (error)
import Node.Path (FilePath)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

type FileSystem = Map FilePath FileBody

newtype TestM a = TestM (StateT FileSystem (ReaderT Env Aff) a)

derive newtype instance functorTestM :: Functor TestM
derive newtype instance applyTestM :: Apply TestM
derive newtype instance applicativeTestM :: Applicative TestM
derive newtype instance bindTestM :: Bind TestM
derive newtype instance monadTestM :: Monad TestM
derive newtype instance monadEffectTestM :: MonadEffect TestM
derive newtype instance monadAskTestM :: MonadAsk Env TestM
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

runTest :: forall a. Env -> FileSystem -> TestM a -> Aff (Tuple a FileSystem)
runTest env init (TestM m) =
  runReaderT (runStateT m init) env

initialFS :: FileSystem
initialFS = Map.empty

spec :: Spec Unit
spec = do
  describe "execute" do
    describe "when File not found" do
      it "should be throw File Not found" do
        result <- attempt $ runTest {} initialFS (execute "./notfound/foo.css" (Namespace "Foo"))
        isLeft result `shouldEqual` true

    describe "when File found" do
      it "should generate correct CSS file" do
        let inputFS = Map.insert "./components/styles.module.css" (FileBody ".foo { display: flex; }") initialFS
        result <- runTest {} inputFS (execute "./components/styles.module.css" (Namespace "Foo"))
        let expectedContent = FileBody """.foo { display: flex; }"""
        case result of
          Tuple _ finalFS -> do
            liftEffect $ log $ show finalFS
            let generatedFile = Map.lookup "output/Foo/styles.module.css" finalFS
            generatedFile `shouldEqual` (Just expectedContent)

      it "should generate correct JS file module" do
        let inputFS = Map.insert "./components/styles.module.css" (FileBody ".foo { display: flex; }") initialFS
        result <- runTest {} inputFS (execute "./components/styles.module.css" (Namespace "Foo"))
        let
          expectedContent = FileBody
            """
import s from "./styles.module.css"
export const _styles = (name) => s[name]
"""
        case result of
          Tuple _ finalFS -> do
            let generatedFile = Map.lookup "components/Styles.module.js" finalFS
            generatedFile `shouldEqual` (Just expectedContent)

      it "should generate correct PureScript module" do
        let inputFS = Map.insert "./components/styles.module.css" (FileBody ".foo { display: flex; }") initialFS
        result <- runTest {} inputFS (execute "./components/styles.module.css" (Namespace "Foo"))
        let
          expectedContent = FileBody
            """module Foo (foo) where
foreign import _styles :: String -> String
foo :: String
foo = _styles "foo""""
        case result of
          Tuple _ finalFS -> do
            let generatedFile = Map.lookup "components/Styles.module.purs" finalFS
            generatedFile `shouldEqual` (Just expectedContent)
