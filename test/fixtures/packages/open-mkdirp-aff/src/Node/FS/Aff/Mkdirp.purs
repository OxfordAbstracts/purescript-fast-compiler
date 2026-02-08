module Node.FS.Aff.Mkdirp (mkdirp) where

import Prelude

import Effect.Aff (Aff, catchError)
import Effect.Class (liftEffect)
import Effect.Exception (Error)
import Node.FS.Aff (mkdir)
import Node.Path (FilePath, dirname, resolve)

foreign import isENOENT :: Error -> Boolean

handleError :: FilePath -> Error -> Aff FilePath
handleError fullPath e =
  if isENOENT e then makeParent fullPath
  else pure fullPath

makeParent :: FilePath -> Aff FilePath
makeParent fullPath = do
  _ <- mkdirp (dirname fullPath)
  mkdirp fullPath

mkdirp :: FilePath -> Aff FilePath
mkdirp p = do
  fullPath <- liftEffect $ resolve [] p
  (mkdir fullPath *> pure p) `catchError` handleError fullPath
