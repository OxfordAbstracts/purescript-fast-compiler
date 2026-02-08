module Test.Lang.PurescriptSpec where

import Test.Prelude

import Data.Map as M
import Data.Tuple.Nested ((/\))
import Effect.Aff (Aff)
import Webb.Writer.Internal as I
import Webb.Writer.Lang.Purescript as Ps
import Webb.Writer.String (trimMargin)

spec :: Spec Unit
spec = describe "Testing writing of Purescript" do
  run "can put a map as a record" do
    let map = M.fromFoldable 
          [ "name" /\ "String"
          , "age" /\ "Int"
          ]
    Ps.putRecord map
    
    outputIs $ trimMargin """
      |{ age : Int
      |, name : String
      |}
      """
      
  run "writing a type" do
    Ps.putType "hello" ["a", "b"]
    outputIs "hello a b"
    
  run "module declaration" do
    Ps.moduleWhere "Test.InternalSpec"
    outputIs "module Test.InternalSpec where"

  run "import" do
    Ps.putImport "Test.InternalSpec as P"
    outputIs "import Test.InternalSpec as P"
    
  run "string literal escapes newline" do
    Ps.string "hello\nthere"
    outputIs "\"hello\\nthere\""
    
  run "multi-line string literal retains newline" do
    Ps.multiLine "hello\nthere"
    outputIs $ "\"\"\"hello\nthere\"\"\""
  
  run "various 'equals' output" do
    Ps.equals *> new
    Ps.typeEquals "hello" *> new
    Ps.bodyEquals "hello" ["a", "b"] *> new
    Ps.newtypeEquals "hello" ["a", "b"] *> new
    Ps.dataEquals "hello" ["a", "b"]
    
    outputIs $ trimMargin """
      |=
      |type hello =
      |hello a b =
      |newtype hello a b =
      |data hello a b =
      """
    

  where
  run msg prog = 
    let p = (do 
          void $ I.execSWriterT I.default do void prog
        ) :: Aff Unit
    in it msg p
    
  outputIs expected = do
    output <- I.getOutput
    output === expected -- actual == expected

  new = I.newline
    

