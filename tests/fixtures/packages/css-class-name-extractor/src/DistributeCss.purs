module CssClassNameExtractor.DistributeCss where

import Prelude

import CssClassNameExtractor.Data.Output (FileBody(..), Namespace, getDistPath, makeCssFile, renderOutput)
import CssClassNameExtractor.FS (class MonadFS, readFile, writeFile)
import Effect.Class (class MonadEffect)
import Node.Path (FilePath, basename)

distributeCss :: forall m. MonadFS m => MonadEffect m => FilePath -> Namespace -> m Unit
distributeCss path ns = do
  styles <- readFile path
  let cssFile = makeCssFile ns (FileBody styles) (basename path)
  writeFile (getDistPath cssFile) (renderOutput cssFile)
