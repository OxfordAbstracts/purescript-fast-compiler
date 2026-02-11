module Webb.Directory where

import Prelude
import Webb.State.Prelude

import Data.Maybe (Maybe)
import Effect.Aff.Class (class MonadAff)
import Webb.Directory.Data.Absolute (AbsolutePath)
import Webb.Directory.Data.Stack (Stack)
import Webb.Directory.Data.Stack as Stack
import Webb.Directory.Internal.Directory as Dir
import Webb.Directory.Visitor (Visitor)
import Webb.Directory.Visitor as Visitor


{- Represents a directory with a stack. This makes it possible to navigate from working directory to working directory, performing operations. The downside of this is that the 
working directory actually _changes_, in case that is important to the scripts that we are launching.
-}

newtype Directory = D
  { stack :: ShowRef Stack
  }
  
derive newtype instance Show Directory

-- Create the new directory object and load in the current working directory
newDirectory :: forall m. MonadAff m => m Directory
newDirectory = do
  stack <- newShowRef Stack.emptyStack
  let dir = D { stack }
  eval dir Dir.init 
  pure dir
  
-- Create the visitor from the top level of the directory.
getVisitor :: forall m. MonadAff m => Directory -> m Visitor
getVisitor dir = do
  current <- currentPath dir
  Visitor.newVisitor current
  
eval :: forall m a. MonadAff m => Directory -> Dir.Prog a -> m a
eval (D s) prog = Dir.eval s prog

currentPath :: forall m. MonadAff m => Directory -> m AbsolutePath
currentPath dir = eval dir Dir.current

parentPath :: forall m. MonadAff m => Directory -> m (Maybe AbsolutePath)
parentPath dir = eval dir Dir.currentParent

files :: forall m. MonadAff m => Directory -> m (Array AbsolutePath)
files dir = eval dir Dir.files

dirs :: forall m. MonadAff m => Directory -> m (Array AbsolutePath)
dirs dir = eval dir Dir.dirs

containsFileName :: forall m. MonadAff m => Directory -> String -> m Boolean
containsFileName dir name = eval dir (Dir.containsFileName name)

containsDirName :: forall m. MonadAff m => Directory -> String -> m Boolean
containsDirName dir name = eval dir (Dir.containsDirName name)

makePath :: forall m. MonadAff m => Directory -> String -> m AbsolutePath
makePath dir name = eval dir (Dir.makeName name)

push :: forall m. MonadAff m => Directory -> AbsolutePath -> m Unit
push dir path = eval dir (Dir.push path)

replace :: forall m. MonadAff m => Directory -> AbsolutePath -> m Unit
replace dir path = eval dir (Dir.replace path)

pop :: forall m. MonadAff m => Directory -> m Unit
pop dir = eval dir (Dir.pop)

popToFirst :: forall m. MonadAff m => Directory -> m Unit
popToFirst dir = eval dir (Dir.popToFirst)

isFirst :: forall m. MonadAff m => Directory -> m Boolean
isFirst dir = eval dir (Dir.isFirst)
