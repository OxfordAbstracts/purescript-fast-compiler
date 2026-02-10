module CssClassNameExtractor.Execute where

import Prelude

import CssClassNameExtractor.CssParser (extractClassNames)
import CssClassNameExtractor.Data.Output (FileBody(..), Namespace, Output, getDistPath, makeCssFile, makeJsFile, makePursFile, renderOutput)
import CssClassNameExtractor.FS (class MonadFS, readFile, writeFile)
import Data.Either (either)
import Data.List (List(..)) as List
import Data.Traversable (traverse)
import Effect.Class (class MonadEffect)
import Node.Path (FilePath, basename)

execute :: forall m. MonadFS m => MonadEffect m => FilePath -> Namespace -> m Unit
execute path namespace = do
  styles <- readFile path
  let classNames = either (const List.Nil) identity (extractClassNames styles)
  let pursFile = makePursFile namespace path classNames
  let jsFile = makeJsFile path
  let cssFile = makeCssFile namespace (FileBody styles) (basename path)
  let outputs = [ jsFile, cssFile, pursFile ]
  traverse writeOutput outputs *> pure unit

  where
  writeOutput :: Output -> m Unit
  writeOutput output = do
    writeFile (getDistPath output) (renderOutput output)

