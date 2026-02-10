module Webb.Writer.Lang.Purescript where

import Prelude
import Webb.Writer.Internal

import Data.Map (Map)
import Data.Map as M
import Data.Tuple (Tuple(..))
import Webb.Writer.ForEach (after, each, forEach_, inBetween)
import Webb.Writer.String (escape)

equals :: forall m. Monad m => SWriterT m Unit
equals = token "="

typeEquals :: forall m . Monad m => String -> SWriterT m Unit 
typeEquals name = do 
  token "type" *> token name *> equals

-- { k1 : v1
-- , k2 : v2
-- }
putRecord :: forall m . Monad m => Map String String -> SWriterT m Unit 
putRecord = putRecord' ":"

-- { k1 :: v1
-- , k2 :: v2
-- }
putRecordType :: forall m . Monad m => Map String String -> SWriterT m Unit 
putRecordType = putRecord' "::"

-- s { k1 = v1
-- , k2 = v2
-- }
putRecordUpdate :: forall m . Monad m => String -> Map String String -> SWriterT m Unit 
putRecordUpdate name map = do 
  token name
  putRecord' "=" map

-- Generator for writing the data.
putRecord' :: forall m. Monad m => String -> Map String String -> SWriterT m Unit 
putRecord' sep map = do
  token "{"
  let arr = M.toUnfoldable map :: Array _
  forEach_ arr do
    each \(Tuple key value') -> do
      token key *> token sep *> token value'
    inBetween \_ -> do
      newline *> token ","
    
  newline
  token "}"
  
-- Write the entire signature.
putSignature :: forall m. Monad m => 
  String -> Array String -> Array String -> Array String -> SWriterT m Unit
putSignature name types classes args = do
  token name *> token "::" *> token "forall"
  forEach_ types do each token

  token "."
  forEach_ classes do
    each token 
    after \_ -> token "=>"

  forEach_ args do
    each token
    inBetween \_ -> token "->"
  
-- Put the initial part of the function body, but not all the body.
bodyEquals :: forall m. Monad m => 
  String -> Array String -> SWriterT m Unit
bodyEquals name args = do
  token name 
  forEach_ args  do each token
  equals

-- Puts the initial part of the newtype.
newtypeEquals :: forall m. Monad m => 
  String -> Array String -> SWriterT m Unit
newtypeEquals name args = do
  token "newtype" *> token name 
  forEach_ args do each token 
  equals 

dataEquals :: forall m. Monad m => 
  String -> Array String -> SWriterT m Unit
dataEquals name args = do 
  token "data" *> token name
  forEach_ args do each token 
  equals
  
-- Write a type, whether that's "Either a b" or "a" or "Boolean"
putType :: forall m. Monad m => String -> Array String -> SWriterT m Unit
putType name args = do
  token name 
  forEach_ args do each token
  
putDo :: forall m. Monad m => SWriterT m Unit
putDo = do token "do"

putAdo :: forall m. Monad m => SWriterT m Unit
putAdo = do token "ado"

moduleWhere :: forall m. Monad m => String -> SWriterT m Unit
moduleWhere m = do
  token "module" *> token m *> token "where"
  
putImport :: forall m. Monad m => String -> SWriterT m Unit
putImport s = token "import" *> token s
  
string :: forall m. Monad m => String -> SWriterT m Unit
string s = do 
  token "\""
  write $ escape s
  write "\""

-- An input multiline string automatically escapes the newlines and tabs so
-- no escaping is needed. That ... should be fine, I think.
multiLine :: forall m. Monad m => String -> SWriterT m Unit
multiLine s = do 
  token "\"\"\"" 
  write s 
  write "\"\"\""