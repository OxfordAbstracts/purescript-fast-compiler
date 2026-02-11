module Data.XML (
  Version(),
  Encoding(),
  Document(..),
  TagName(),
  Node(..),
  Attr(..)
  ) where

type Version = String
type Encoding = String
data Document = Document Version Encoding Node

type TagName = String
data Node = Element TagName (Array Attr) (Array Node)
          | Text String
          | Comment String

data Attr = Attr String String
