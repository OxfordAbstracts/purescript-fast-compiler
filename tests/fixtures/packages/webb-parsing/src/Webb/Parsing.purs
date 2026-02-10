module Webb.Parsing
  ( column
  , filePosition
  , index
  , line
  )
  where

import Prelude
import Parsing


filePosition :: forall m s. ParserT s m { line :: Int, column :: Int }
filePosition = do
  Position s <- position
  pure { line: s.line, column: s.column }

line :: forall m s. ParserT s m Int
line = do 
  Position s <- position
  pure s.line

column :: forall m s. ParserT s m Int
column = do 
  Position s <- position
  pure s.column

index :: forall m s. ParserT s m Int
index = do 
  Position s <- position
  pure s.index