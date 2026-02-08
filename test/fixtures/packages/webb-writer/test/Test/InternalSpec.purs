module Test.InternalSpec where

import Test.Prelude

import Effect.Aff (Aff)
import Webb.Writer.Internal as I
import Webb.Writer.String (trimMargin)


spec :: Spec Unit
spec = describe "Testing internals of writing" do
  run "view output" do
    outputIs ""
    posIs I.defaultPos
    
  run "simple write" do 
    I.write "abc"
    outputIs "abc"
    posIs $ I.defaultPos { column = 3 }
    
  run "write a newline" do
    I.write "abc\n"
    outputIs "abc\n"
    posIs $ I.defaultPos { column = 0, line = 1 }

  run "write multiple newlines" do
    I.write "\na\nb\n"
    outputIs "\na\nb\n"
    posIs $ I.defaultPos { 
      column = 0
    , line = 3
    }
    
  run "ensure single-line indent" do
    I.withIndent 2 do
      I.write "abc"
    outputIs "  abc"
    posIs $ I.defaultPos {
      indentSpaces = 0
    , line = 0
    , column = 5 -- We were indented
    }

  run "indent with newline" do
    I.withIndent 2 do
      I.write "abc\n"
    outputIs "  abc\n"
    posIs $ I.defaultPos {
      indentSpaces = 0
    , line = 1
    , column = 0 -- Newline goes to 0, until attempt to write.
    }
    
  run "ensure multi-line, nested indent" do
    I.withIndent 2 do
      I.write "a\n"
      I.withIndent 2 do
        I.write "b\n"
      I.write "c"
      
    outputIs $ trimMargin """
      |  a
      |    b
      |  c
      """
      
    posIs $ I.defaultPos {
      indentSpaces = 0
    , line = 2
    , column = 3 -- We were indented
    }
    
  run "token adds a space if the previous character was a non-space" do
    I.tokens ["a", "b", "c"]
    outputIs "a b c"

    posIs $ I.defaultPos {
      indentSpaces = 0
    , line = 0
    , column = 5
    }
    
  run "token adds a space after start of line" do
    I.write "a"
    I.token "b"
    outputIs "a b"
    
    posIs $ I.defaultPos {
      indentSpaces = 0
    , line = 0
    , column = 3 
    }
    
  run "token will not add space at start of line" do
    I.withIndent 2 do
      I.token "a\n"
      I.withIndent 2 do
        I.token "b\n"
        I.token "c"
        I.token "d"
        
    outputIs $ trimMargin """
      |  a
      |    b
      |    c d
      """
      
    posIs $ I.defaultPos {
      indentSpaces = 0
    , line = 2
    , column = 7
    }
      
  run "can add a newline safely" do
    I.newline
    I.newline
    outputIs $ "\n\n"
      
  where
  run msg prog = 
    let p = (do 
          void $ I.execSWriterT I.default do void prog
        ) :: Aff Unit
    in it msg p
    
  outputIs expected = do
    output <- I.getOutput
    output === expected -- actual == expected

  posIs expected = do
    pos <- I.getPosition
    pos === expected
    
