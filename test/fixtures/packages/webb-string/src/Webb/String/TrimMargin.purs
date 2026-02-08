module Webb.String.TrimMargin where

import Prelude

import Control.Monad.Loops (whileM_)
import Control.Monad.State (State, evalState)
import Data.Array (foldl)
import Data.Maybe (isJust)
import Data.String (CodePoint)
import Data.String as S
import Data.String.CodePoints as CP
import Data.Tuple.Nested ((/\))
import Webb.Array as A
import Webb.State.Prelude (mmodify_, mreads)

{- A helper for writing multiline strings. As in:

```
  where
  string = trimMargin """
    | hello, there!
    | how have you been?
  """
```

Only the lines starting with a '|' character will be treated as valid lines. Everything else will be discarded.
-}

-- Escape particular characters in a string, replacing them with
-- new values
escape :: String -> String
escape s = let 
  chars = [ "\n" /\ "\\n", "\t" /\ "\\t", "\r" /\ "\\r"  ]
  in foldl escape_ s chars
  where
  escape_ acc (char /\ replace) = 
    S.replace (S.Pattern char) (S.Replacement replace) acc

type TrimMargin = 
  { lines :: Array (Array CodePoint)
  , remaining :: Array CodePoint
  , continue :: Boolean
  }

-- Remove margin from front of string. Each valid line is indicated by a 
-- margin indicator '|'. This is useful for multiline strings.
trimMargin :: String -> String
trimMargin str = flip evalState init do
  lines <- extractLines
  pure $ S.joinWith "\n" lines
  where
  init = { lines: [], remaining: S.toCodePointArray str, continue: true }

  extractLines :: State TrimMargin (Array String)
  extractLines = do
    whileM_ shouldContinue do
      success <- dropMargin
      if success then do
        takeLine
      else do
        quit

    mreads $ _.lines >>> (_ <#> S.fromCodePointArray)
        
  -- Try to drop until the margin, if it exists.
  dropMargin = do
    rem <- mreads _.remaining
    let hasMargin = isJust $ A.find isMargin rem
    when hasMargin do
      let withoutMargin = A.dropWhileIncl notMargin rem
      mmodify_ $ _ { remaining = withoutMargin }
    pure hasMargin
    
  -- Take a line, stopping at end of string, or at \n
  takeLine = do
    rem <- mreads _.remaining
    let line = A.takeWhileExcl notNewline rem
        withoutLine = A.dropWhileExcl notNewline rem
    mmodify_ $ \s -> s
      { lines = A.snoc s.lines line
      , remaining = withoutLine
      }
    
  isMargin cp = CP.singleton cp == "|"
  notMargin = not <<< isMargin

  isNewline cp = CP.singleton cp == "\n"
  notNewline = not <<< isNewline
        
  shouldContinue = do mreads _.continue
  quit = do mmodify_ $ _ { continue = false }

    

