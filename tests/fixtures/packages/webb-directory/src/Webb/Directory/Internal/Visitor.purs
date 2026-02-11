module Webb.Directory.Internal.Visitor where

import Prelude
import Webb.State.Prelude

import Control.Monad.State (StateT)
import Control.Monad.State as State
import Data.Array as Array
import Data.Maybe (Maybe)
import Data.Set as Set
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Node.FS.Aff as File
import Node.FS.Stats as Stat
import Webb.Directory.Data.Absolute (AbsolutePath, (++))
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Data.Stack (Stack)
import Webb.Directory.Data.Stack as Stack
import Webb.Monad.Prelude (forceMaybe')


{- Define internal directory stack. However, init proceeds differently, and we 
  NEVER rely on the CWD for any operations.
-}

type State = { stack :: ShowRef Stack }
type Path = String

type Prog = StateT State Aff

eval :: forall m a. MonadAff m => State -> Prog a -> m a
eval state prog = liftAff do 
  State.evalStateT prog state

-- Initialize the stack with the current working directory
init :: AbsolutePath -> Prog Unit
init path = do
  this <- mread
  Stack.push path :> this.stack
  
isFirst :: Prog Boolean
isFirst = do
  this <- mread
  size' <- Stack.size <: this.stack
  pure $ size' <= 1

size :: Prog Int
size = do 
  this <- mread
  Stack.size <: this.stack

toString :: Prog String
toString = do 
  this <- mread
  pure $ show this.stack
  
-- Push the next directory onto the stack, and navigate there.
-- Allows relative paths to be used.
push :: AbsolutePath -> Prog Unit
push dir = do
  this <- mread
  Stack.push dir :> this.stack

-- Pop to the previous working directory.
pop :: Prog Unit
pop = do
  this <- mread
  size' <- Stack.size <: this.stack
  when (size' > 1) do
    Stack.pop :> this.stack

-- Pop to the first working directory.
popToFirst :: Prog Unit
popToFirst = do
  this <- mread
  size' <- Stack.size <: this.stack
  when (size' > 1) do
    Stack.popToFirst :> this.stack
    
-- Replace the existing current directory and navigate to it.
replace :: AbsolutePath -> Prog Unit
replace dir = do
  this <- mread
  Stack.replace dir :> this.stack
  
-- What is the current directory, according to our stack?
current :: Prog AbsolutePath
current = do
  this <- mread
  mpath <- Stack.peek <: this.stack
  path <- forceMaybe' "Expected a stack top to exist" mpath
  pure $ path
  
-- Get the parent path, if it exists.
currentParent :: Prog (Maybe AbsolutePath)
currentParent = do 
  path <- current
  let mparent = Abs.parent path
  pure mparent
  
-- Publishes all the paths as absolute paths.
currentPaths :: Prog (Array AbsolutePath)
currentPaths = do
  path <- current
  paths <- File.readdir (Abs.unwrap path) # liftAff
  pure $ paths <#> flip Abs.child path

-- What are the files in the current directory?
-- If we have them, we can operate on them.
files :: Prog (Array AbsolutePath)
files = do
  paths <- currentPaths
  arr <- Array.filterA isFile paths
  pure $ arr 
  
-- Do we have the given file name?
containsFileName :: String -> Prog Boolean
containsFileName name = do
  paths <- files
  let names = Abs.basename <$> paths
  pure $ Set.member name $ Set.fromFoldable names

-- What are the sub-directories in the current directory?
-- If we have them, we can operate on them. But these are all _absolute_ paths.
-- We can navigate down into them.
dirs :: Prog (Array AbsolutePath)
dirs = do 
  paths <- currentPaths
  arr <- Array.filterA isDirectory paths
  pure $ arr
  
-- Do we have the given directory name?
containsDirName :: String -> Prog Boolean
containsDirName name = do
  paths <- dirs
  let names = Abs.basename <$> paths
  pure $ Set.member name $ Set.fromFoldable names
  
-- Take the current directory and append the string. Useful for creating a path for a file -- -- if we detect a "spago.yaml", we can obtain its path with ease.
makeName :: String -> Prog AbsolutePath
makeName string = do
  path <- current
  pure $ path ++ string
  
-- Is the given path a _file_? This will not change based on the cwd.
isFile :: AbsolutePath -> Prog Boolean
isFile path = do 
  stat <- File.stat (Abs.unwrap path) # liftAff
  pure $ Stat.isFile stat

-- Is the given path a _directory_? This will not change based on the cwd.
isDirectory :: AbsolutePath -> Prog Boolean
isDirectory path = do
  stat <- File.stat (Abs.unwrap path) # liftAff
  pure $ Stat.isDirectory stat