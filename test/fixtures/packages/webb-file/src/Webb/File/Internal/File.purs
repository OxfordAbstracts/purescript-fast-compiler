module Webb.File.Internal.File where

import Prelude
import Webb.State.Prelude

import Control.Monad.Loops (whileM_)
import Control.Monad.State (StateT, evalStateT)
import Data.Array as Array
import Data.Foldable (for_)
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Data.Tuple (fst)
import Data.Tuple.Nested ((/\), type (/\))
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Node.Buffer (Buffer)
import Node.Buffer as Buffer
import Node.Encoding (Encoding(..))
import Node.FS (FileFlags(..))
import Node.FS.Aff as FS
import Node.FS.Stats as Stat
import Webb.Directory.Data.Absolute as Abs
import Webb.File.Data.File as File
import Webb.Monad.Prelude (forceMaybe', notM, (&&=))
import Webb.Stateful.ArrayColl as ArrayColl



{- Program for how the file works internally. All a file does is give enough 
  API exposure to think clearly about file operations.
-}


type State = 
  { file :: ShowRef File.File
  }
  
type Prog = StateT State Aff

eval :: forall a. State -> Prog a -> Aff a
eval state prog = evalStateT prog state

path :: Prog Abs.AbsPath
path = do
  this <- mread
  File.path <: this.file

position :: Prog Int
position = do
  this <- mread
  File.position <: this.file

forceFd :: Prog File.Fd
forceFd = do
  this <- mread
  mfd <- File.fd <: this.file
  forceMaybe' "File was not open" mfd

isAppending :: Prog Boolean
isAppending = do
  this <- mread
  File.isAppending <: this.file

isOpen :: Prog Boolean
isOpen = do
  this <- mread
  File.isOpen <: this.file

isClosed :: Prog Boolean
isClosed = notM isOpen

-- If the file isn't open, open it, creating it if necessary, and truncating
-- it if it already exists.
openTruncated :: Prog Unit
openTruncated = do
  this <- mread
  abs <- path
  whenM isClosed do
    fd <- FS.fdOpen (Abs.unwrap abs) W_PLUS Nothing # liftAff
    File.loadFd fd >>> File.setPosition 0 >>>
      File.appending false :> this.file

-- If the file isn't open, open it and create it if necessary. Writes will
-- only append.
openAppending :: Prog Unit
openAppending = do
  this <- mread
  abs <- path
  whenM isClosed do
    fd <- FS.fdOpen (Abs.unwrap abs) A_PLUS Nothing # liftAff
    File.loadFd fd >>> File.setPosition 0 >>>
      File.appending true :> this.file
    
-- If the file isn't open, open it and create it if necessary, pointing to
-- the start of the file. But the write takes place at the current position.
open :: Prog Unit
open = do
  ensureExists

  this <- mread
  abs <- path
  whenM isClosed do
    fd <- FS.fdOpen (Abs.unwrap abs) R_PLUS Nothing # liftAff
    File.loadFd fd >>> File.setPosition 0 >>>
      File.appending false :> this.file
  where
  ensureExists = do openAppending *> close

-- Closes the current fd, if it exists.
close :: Prog Unit
close = do
  this <- mread
  mfd <- File.fd <: this.file
  for_ mfd \fd -> do
    File.unloadFd :> this.file 
    FS.fdClose fd # liftAff
    
-- Number of bytes in the file. If 0, the number could not
-- be determined.
size :: Prog Int
size = do
  abs <- path
  stat <- FS.stat (Abs.unwrap abs) # liftAff
  let int = Int.fromNumber $ Stat.size stat
  pure $ fromMaybe 0 int
  
-- If the file isn't open, truncate it to the desired length.
truncate :: Int -> Prog Unit
truncate n =  do 
  abs <- path
  FS.truncate (Abs.unwrap abs) n # liftAff

  -- To keep valid position, including if truncation is too LARGE
  -- for the file, we move our position to stay in alignment.
  pos <- position
  newSize <- size
  seek (min pos newSize)
  
-- Seek the file's position to a particular place in the file. The File
-- always performs read/write operations from its current position.
-- cannot seek to a negative number.
seek :: Int -> Prog Unit
seek n = do
  this <- mread
  size' <- size
  let maxPos = max 0 (size') -- At position 'size', we are writing to end of file.
  File.setPosition (clamp 0 maxPos n) :> this.file

-- Change the file's position by a relative amount.
seekBy :: Int -> Prog Unit
seekBy n = do
  pos <- position
  let newPos = pos + n
  seek newPos
  
-- Writes the buffer to file at the current file position -- but if the file
-- was opened as an 'APPENDING' file, it will always write to the end.
-- We always write the ENTIRE buffer, for simplicity, since I'm not
-- doing much buffer management.
writeBuffer :: Buffer -> Prog Unit
writeBuffer buf = do
  pos <- position
  fd <- forceFd
  append <- isAppending
  length <- Buffer.size buf # liftEffect

  if append then do
    -- An append file _should_ write to the end, naturally.
    void (FS.fdWrite fd buf 0 length Nothing) # liftAff
  else do
    -- We only advance the file position if it wasn't an append.
    void (FS.fdWrite fd buf 0 length $ Just pos) # liftAff
    seekBy length -- We advance the file position.
  
-- Are we at the end? We're at the end if attempting to read does nothing.
isEof :: Prog Boolean
isEof = do
  ifM isOpen (do
    _buffer /\ count <- peekBuffer 1
    pure $ count <= 0
  ) (do 
    pure false
  )

-- Peek the next `n` notes at the current position.
-- Buffer size consists ONLY of values that were read, so no count of the buffer
-- is needed.
peekBuffer :: Int -> Prog (Buffer /\ Int)
peekBuffer n = do
  pos <- position
  fd <- forceFd
  buffer <- Buffer.create n # liftEffect
  count <- FS.fdRead fd buffer 0 n (Just pos) # liftAff
  pure $ take count buffer /\ count

  where
  -- limit the buffer to size N
  take n' buffer = let 
    minimalBuffer = Buffer.slice 0 n' buffer
    in minimalBuffer
  
-- From the file position, attempt to read N bytes. Return a byte buffer and
-- the number of bytes that was actually read.
readBuffer :: Int -> Prog (Buffer /\ Int)
readBuffer n = do
  result@(_buffer /\ count) <- peekBuffer n
  seekBy count -- advance the recorded position after reading.
  pure result
  
-- Write a string of length N with UTF-8 encoding, since UTF-8 is best-supported
-- and is compatible with ASCII; UTF-16 is incompatible.
writeString :: String -> Prog Unit
writeString s = do
  buf <- Buffer.fromString s UTF8 # liftEffect
  writeBuffer buf

-- Reads a string of length N with UTF-8 encoding
readString :: Int -> Prog String
readString n = do
  let maxCount = n * 4
  buffer <- fst <$> peekBuffer maxCount -- Only peek. Don't change file position.
  string <- Buffer.toString UTF8 buffer # liftEffect
  prefix <- getPrefix string
  moveForwardBy prefix
  pure prefix
  
  where

  getPrefix str = do
    pure $ String.take n str

  moveForwardBy str = do
    -- When we've found the right count, _then_ we change it.
    stringSize <- byteCount str
    seekBy stringSize 

-- Read a line in UTF8. The newline is discarded.
-- Checking for EOF should be done separately.
readLine :: Prog String
readLine = readLineSepBy "\n"

readLineSepBy :: String -> Prog String
readLineSepBy sep = readLineSepBy' 256 sep

-- Separate lines by a custom string delimiter. The delimiter is ignored
-- in what is read. Checking for EOF should be done separately.
-- We assume a (hopefully reasonable) chunk size, and continue until we find
-- the delimiter.
readLineSepBy' :: Int -> String -> Prog String
readLineSepBy' chunkSize sep = do
  strings <- ArrayColl.newArray
  continue <- newShowRef true
  
  whileM_ (hasMoreAnd continue) do
    buffer <- fst <$> peekBuffer chunkSize
    string <- Buffer.toString UTF8 buffer # liftEffect

    if hasSep string then do
      -- Add the last part of the line, and then stop.
      prefix <- getPrefix string
      ArrayColl.addLast strings prefix
      moveFileForwardBy prefix
      moveFileForwardBy sep
      continue := false
    else do 
      -- Pattern was not found. Add the ENTIRE string and then continue.
      ArrayColl.addLast strings string
      moveFileForwardBy string
      continue := true
    
  actualString <- getString strings
  pure actualString
  
  where 
  hasMoreAnd continue = (notM isEof &&= aread continue)

  hasSep str = String.contains (String.Pattern sep) str
  
  getPrefix str = do 
    let 
      splits = String.split (String.Pattern sep) str
      mprefix = Array.head splits
    forceMaybe' "Expected prefix before the separator" mprefix
  
  getString strings = do
    chunks <- aread strings
    pure $ String.joinWith "" chunks
    
  moveFileForwardBy string = do
    stringSize <- byteCount string
    seekBy stringSize
    
byteCount :: String -> Prog Int
byteCount string = do
  buffer <- Buffer.fromString string UTF8 # liftEffect
  count <- Buffer.size buffer # liftEffect
  pure count

readAllText :: Prog String
readAllText = do
  p <- path
  let path' = Abs.unwrap p
  FS.readTextFile UTF8 path' # liftAff

writeAllText :: String -> Prog Unit
writeAllText text = do
  p <- path
  let path' = Abs.unwrap p
  FS.writeTextFile UTF8 path' text # liftAff