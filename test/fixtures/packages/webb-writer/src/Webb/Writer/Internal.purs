module Webb.Writer.Internal where

import Prelude

import Control.Monad.State (StateT, evalStateT, execStateT, lift, runStateT)
import Data.Array as A
import Data.Array as Array
import Data.CodePoint.Unicode as Unicode
import Data.Foldable (for_)
import Data.Identity (Identity)
import Data.Maybe (Maybe, fromMaybe)
import Data.Newtype (unwrap)
import Data.String (CodePoint, Pattern(..), Replacement(..))
import Data.String as Str
import Data.String as String
import Data.Tuple (Tuple)
import Webb.Monad.Prelude (timesRepeat_)
import Webb.State.Prelude (mmodify_, mread, mreads, mwrite)
import Webb.Writer.ForEach (each, forEach_, inBetween)


{- The writer monad enables us to write to the monoidal source. It has to maintain the indent level in such a way that changes after a newline. Thus, we write to a thing, and utilize the indent level. Newlines ... are special. To prevent newlines from causing a problem, though, perhaps we have to count the newlines and reset the indent level when needed.
-}

type St = 
  { indentSpaces :: Int
  , line :: Int
  , column :: Int
  , output :: Array String
  , lastWrite :: String
  }

type Position = 
  { indentSpaces :: Int
  , line :: Int
  , column :: Int
  }

type StringWriterT = StateT St
type SWriterT = StringWriterT
type SWriter = SWriterT Identity

default :: St
default = 
  { indentSpaces: 0
  , line: 0
  , column: 0
  , output: []
  , lastWrite: ""
  }

defaultPos :: Position
defaultPos = 
  { indentSpaces: 0
  , line: 0
  , column: 0
  }
  
-- Run a writer to a string -- good for building a string with ease.
runToString :: SWriter Unit -> String
runToString prog = let 
  state = unwrap $ execSWriterT default prog :: St
  in String.joinWith "" state.output

execSWriterT :: forall m a. Monad m => St -> SWriterT m a -> m St
execSWriterT pos prog = do execStateT prog pos

evalSWriterT :: forall m a. Monad m => St -> SWriterT m a -> m a
evalSWriterT pos prog = do evalStateT prog pos

runSWriterT :: forall m a. Monad m => St -> SWriterT m a -> m (Tuple a St)
runSWriterT pos prog = do runStateT prog pos

getPosition :: forall m. Monad m => SWriterT m Position
getPosition = do 
  st <- mread
  pure $ { indentSpaces: st.indentSpaces, line: st.line, column: st.column }

getOutput :: forall m. Monad m => SWriterT m String
getOutput = do mreads $ _.output >>> Str.joinWith ""

clearOutput :: forall m. Monad m => SWriterT m Unit
clearOutput = do mmodify_ $ _ { output = [] }

lastCodePoint :: forall m. Monad m => SWriterT m (Maybe CodePoint)
lastCodePoint = do
  st <- mread
  let points = String.toCodePointArray st.lastWrite
  pure $ Array.last points

-- Write a string. Ensure it is a separate token -- if the previous character
-- was _not_ whitespace, add a space so that it's a separate word.
token :: forall m. Monad m => String -> SWriterT m Unit
token t = do 
  whenM needsExtraSpace do write " "
  write t
  where
  -- Do we need to print a space beforehand? We only need it if
  -- the last character written was NOT a space.
  needsExtraSpace :: SWriterT m Boolean
  needsExtraSpace = do
    mpoint <- lastCodePoint
    pure $ fromMaybe false do
      point <- mpoint
      pure $ not (Unicode.isSpace point)

-- Write multiple tokens to the stream as an array.
tokens :: forall m. Monad m => Array String -> SWriterT m Unit
tokens arr = do for_ arr token

word :: forall m. Monad m => String -> SWriterT m Unit
word = token

words :: forall m. Monad m => Array String -> SWriterT m Unit
words arr = do for_ arr word

-- Add an indent to the current indent, requiring all subsequent writes to
-- be at that indent or later. Restore the current indent once the inner program
-- is done running.
withIndent :: forall m. Monad m => Int -> SWriterT m Unit -> SWriterT m Unit
withIndent n prog = do 
  old <- mread
  let indented = old { indentSpaces = old.indentSpaces + n }
  new <- execSWriterT indented prog # lift
  let final = new { indentSpaces = old.indentSpaces }
  mwrite final 

indent :: forall m. Monad m => Int -> SWriterT m Unit -> SWriterT m Unit
indent = withIndent

-- Write a string. Respect the current indent, even as newlines occur in the string.
write :: forall m. Monad m => String -> SWriterT m Unit
write str = do
  when (str /= "") do
    let split = str # Str.split (Pattern "\n")
        lines = A.filter (_ /= "") split
        beforeCount = split # A.takeWhile (_ == "") >>> A.length
        afterCount = split # A.reverse >>> A.takeWhile (_ == "") >>> A.length
        mapped = lines <#> Str.replace (Pattern "\t") (Replacement $ spaces 2)
        
    if A.length lines == 0 then
      timesRepeat_ (max 0 (beforeCount - 1)) do addNewLine
    else do
      timesRepeat_ beforeCount do addNewLine

      forEach_ mapped do 
        each addToLine
        inBetween \_ -> addNewLine
        
      timesRepeat_ afterCount do addNewLine

  where
  -- Adding to the line always bumps to the requested indent if the current
  -- column isn't there yet.
  addToLine :: String -> SWriterT m Unit
  addToLine x = do
    prefix <- getIndentPrefix
    let appendData = if prefix == "" then [x] else [prefix, x]
        appendLen = Str.length prefix + Str.length x
    mmodify_ \s -> s { 
      output = s.output <> appendData
    , column = s.column + appendLen
    , lastWrite = String.joinWith "" appendData
    }
    
  getIndentPrefix :: SWriterT m String
  getIndentPrefix = do
    s <- mread
    let len = max 0 (s.indentSpaces - s.column)
        prefix = Str.joinWith "" (A.replicate len " ")
    pure prefix
    
  addNewLine :: SWriterT m Unit
  addNewLine = do
    mmodify_ \s -> s {
      output = A.snoc s.output "\n"
    , column = 0
    , line = s.line + 1
    , lastWrite = "\n"
    }
    
  spaces i = Str.joinWith "" $ A.replicate i " "

newline :: forall m . Monad m => SWriterT m Unit 
newline = do write "\n"
