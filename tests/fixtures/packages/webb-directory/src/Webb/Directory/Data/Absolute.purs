module Webb.Directory.Data.Absolute where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Node.Path as Path
import Node.Process as Process
import Webb.Stateful (localEffect)

type Path = String

newtype AbsolutePath = AP Path
derive newtype instance Eq AbsolutePath
derive newtype instance Ord AbsolutePath
derive newtype instance Show AbsolutePath

type AbsPath = AbsolutePath

-- Resolve a path. An empty array resolves to the root directory "/"
-- A simple name without any preceding directory indicator resolves relative to
-- to the current directory; so ["hello"] becomes ["./hello"]. To get "/hello", use 
-- `new ["/", "hello"]` or `new [] "/hello"`
new :: Array Path -> Path -> AbsolutePath
new dir path = localEffect do 
  str <- Path.resolve dir path
  pure $ AP str

newAbs :: Array Path -> Path -> AbsolutePath
newAbs = new

modify :: (String -> String) -> AbsolutePath -> AbsolutePath
modify f (AP str) = AP (f str)
  
unwrap :: AbsolutePath -> Path
unwrap (AP str) = str

cwd :: Unit -> AbsolutePath
cwd _ = localEffect do
  path <- Process.cwd
  pure $ new [] path

basename :: AbsolutePath -> String
basename (AP str) = Path.basename str

-- Get the parent path of this path, if it exists
parent :: AbsolutePath -> Maybe AbsolutePath
parent this@(AP str) = let 
  p = new [str] ".."
  in if p == this then
    Nothing
  else 
    Just p

-- Treat the subsequent string as an attempt to _extend_ the path, allowing
-- ".." if the desire is to go upward, or "/child" or "child" if the desire is to go
-- downward.
child :: String -> AbsolutePath -> AbsolutePath
child extension (AP str) = let
  normal = Path.concat $ [ str, extension ]
  c = new [] normal
  in c

childFlipped :: AbsolutePath -> String -> AbsolutePath
childFlipped = flip child

-- path ++ "goodbye" ++ "../hello"
infixl 5 childFlipped as ++

asString :: AbsolutePath -> String
asString = unwrap

-- How deep is the path in the file system? We can only determine this 
-- by separating the string path's segments, and counting. We make no distinction
-- here between files and directories -- it is up to the caller to tell the 
-- difference.
depth :: AbsolutePath -> Int
depth (AP str) = let 
  segments = String.split (String.Pattern Path.sep) str
  filtered = Array.filter (_ /= "") segments
  in Array.length filtered