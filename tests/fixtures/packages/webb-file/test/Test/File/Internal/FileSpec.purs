module Test.File.Internal.FileSpec where

import Test.Prelude

import Data.String as String
import Effect.Aff (finally)
import Effect.Class (liftEffect)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Test.Spec (around_)
import Webb.Directory.Data.Absolute as Abs
import Webb.File.Data.File as FileData
import Webb.File.Internal.File as File

spec :: Spec Unit
spec = describe "File internal tests" do 
  around_ resetExample do 
    run "test empty" do
      posIs 0
      appendingIs false
      openIs false
      eofIs false
      sizeIs 5 -- "hello"
      
    run "read entire file" do
      str <- File.readAllText
      str === "hello"

    run "write entire file" do
      File.writeAllText "unicorn"
      textIs "unicorn"
      
    run "normal open and close" do 
      File.open
      openIs true
      eofIs false
      File.close
      openIs false
      eofIs false
      
    run "read strings" do 
      File.open
      s1 <- File.readString 0
      s1 === ""
      eofIs false

      s2 <- File.readString 1
      s2 === "h"

      s3 <- File.readString 2
      s3 === "el"

      s4 <- File.readString 5
      s4 === "lo"
      eofIs true
      posIs 5
      
    run "write strings" do
      File.open
      File.writeString ""
      textIs "hello"
      File.writeString "si"
      textIs "sillo"
      File.writeString "ppy"
      textIs "sippy"
      File.writeString "Cup"
      textIs "sippyCup"
      sizeIs 8
      posIs 8
      
    run "truncate file" do
      File.open
      File.truncate 1
      textIs "h"
      sizeIs 1
      posIs 0
      s <- File.readString 1
      s === "h"

    run "truncate while position is beyond" do
      File.open
      File.seek 1
      File.truncate 1
      textIs "h"
      posIs 1
      s <- File.readString 1
      s === ""
      
    run "open-truncate and write" do
      File.openTruncated
      sizeIs 0
      textIs ""
      File.writeString "gypsy"
      textIs "gypsy"
      sizeIs 5
      posIs 5
      
    run "open-append and write" do
      File.openAppending

      File.writeString ","
      let text = "hello,"
      textIs text
      sizeIs $ String.length text
      posIs 0

      File.writeString " world!"
      let text' = "hello, world!"
      textIs text'
      sizeIs $ String.length text'
      posIs 0
      
    run "read and seek" do
      File.open
      s <- File.readString 1
      s === "h"
      File.seek 4 -- index 4 of "hello"
      s' <- File.readString 1
      s' === "o"
      eofIs true

      File.seek 5000
      s'' <- File.readString 1
      s'' === ""
      eofIs true
      posIs 5
      
    run "write and seek" do
      File.open
      File.seek 2
      File.writeString "a"
      textIs "healo"
      posIs 3
      
      File.seek 5000
      File.writeString "n"
      textIs "healon"
      posIs 6
      
    run "reads lines of separated strings" do
      File.open
      let text = "\nhello\ngoodbye\n"
      File.writeAllText text
      s <- readLine 
      s === ""

      s1 <- readLine
      s1 === "hello"
      eofIs false

      s2 <- readLine
      s2 === "goodbye"
      eofIs true

      s3 <- readLine
      s3 === ""
      eofIs true
      posIs $ String.length text
      
    run "reads one line, unseparated" do
      File.open
      let text = "hello"
      s <- readLine 
      s === "hello"
      eofIs true
      posIs $ String.length text
      
  where
  posIs n = do
    p <- File.position
    p === n
    
  appendingIs bool = do
    is <- File.isAppending
    is === bool
    
  openIs bool = do
    is <- File.isOpen
    is === bool
    
  sizeIs n = do
    size <- File.size
    size === n

  eofIs bool = do
    is <- File.isEof
    is === bool
  
  textIs str = do
    text <- File.readAllText
    text === str
    
  readLine = do File.readLineSepBy' 1 "\n"

  run msg prog = do 
    it msg do 
      state <- FileData.emptyFile (Abs.new ["./test-data"] "example.txt") # liftEffect
      file <- newShowRef state
      let env = { file }
      finally
        (File.eval env do File.close) -- Ensure file gets closed each time.
        (File.eval env do void $ prog)
  
  resetExample runTest = do
    setExample
    finally 
      setExample 
      runTest
    
  setExample = do
    FS.writeTextFile UTF8 "./test-data/example.txt" "hello"

