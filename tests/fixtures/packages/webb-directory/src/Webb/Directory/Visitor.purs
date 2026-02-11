module Webb.Directory.Visitor where

import Prelude
import Webb.State.Prelude

import Data.Array as Array
import Data.Maybe (Maybe)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Node.Process as Process
import Webb.Directory.Data.Absolute (AbsolutePath)
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Data.Stack (Stack)
import Webb.Directory.Data.Stack as Stack
import Webb.Directory.Internal.Visitor as Vis


{- Implement a directory visitor. It does NOT affect the current working directory, but does allow movement from directory to directory, while maintaining a stack so we can return to prior directories.
-}

newtype Visitor = D
  { stack :: ShowRef Stack
  }
  
derive newtype instance Show Visitor

-- Create the new visitor object and load in the current working directory
newVisitor :: forall m. MonadAff m => AbsolutePath -> m Visitor
newVisitor path = do
  stack <- newShowRef Stack.emptyStack
  let vis = D { stack }
  eval vis $ Vis.init path
  pure vis

newCurrentVisitor :: forall m. MonadAff m => m Visitor
newCurrentVisitor = do
  cwd <- Process.cwd # liftEffect
  let path = Abs.newAbs [] cwd
  newVisitor path
  
eval :: forall m a. MonadAff m => Visitor -> Vis.Prog a -> m a
eval (D s) prog = Vis.eval s prog

currentPath :: forall m. MonadAff m => Visitor -> m AbsolutePath
currentPath dir = eval dir Vis.current

parentPath :: forall m. MonadAff m => Visitor -> m (Maybe AbsolutePath)
parentPath dir = eval dir Vis.currentParent

childCount :: forall m. MonadAff m => Visitor -> m Int
childCount vis = eval vis do
  Array.length <$> Vis.currentPaths

files :: forall m. MonadAff m => Visitor -> m (Array AbsolutePath)
files dir = eval dir Vis.files

dirs :: forall m. MonadAff m => Visitor -> m (Array AbsolutePath)
dirs dir = eval dir Vis.dirs

containsFileName :: forall m. MonadAff m => Visitor -> String -> m Boolean
containsFileName dir name = eval dir (Vis.containsFileName name)

containsDirName :: forall m. MonadAff m => Visitor -> String -> m Boolean
containsDirName dir name = eval dir (Vis.containsDirName name)

makePath :: forall m. MonadAff m => Visitor -> String -> m AbsolutePath
makePath dir name = eval dir (Vis.makeName name)

push :: forall m. MonadAff m => Visitor -> AbsolutePath -> m Unit
push dir path = eval dir (Vis.push path)

replace :: forall m. MonadAff m => Visitor -> AbsolutePath -> m Unit
replace dir path = eval dir (Vis.replace path)

pop :: forall m. MonadAff m => Visitor -> m Unit
pop dir = eval dir (Vis.pop)

popToFirst :: forall m. MonadAff m => Visitor -> m Unit
popToFirst dir = eval dir (Vis.popToFirst)

isFirst :: forall m. MonadAff m => Visitor -> m Boolean
isFirst dir = eval dir (Vis.isFirst)
