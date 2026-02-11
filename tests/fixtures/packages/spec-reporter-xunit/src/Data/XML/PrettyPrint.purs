module Data.XML.PrettyPrint (
  Indent(),
  print
  ) where

import Prelude

import Control.Monad.State (runStateT, get, lift, modify, StateT)
import Control.Monad.Writer (execWriter, tell, Writer)
import Data.Array (replicate)
import Data.Either (Either(Right, Left))
import Data.Foldable (foldl, sequence_)
import Data.String (Pattern(Pattern), split)
import Data.String.CodeUnits (fromCharArray)
import Data.String.Regex (regex, replace')
import Data.String.Regex.Flags as Flags
import Data.XML as XML

type Indent = Int
type CurrentIndent = Int

-- | The number of spaces in an indent and the current number of indents made.
-- | `PrinterState 2 6` represents 12 spaces.
data PrinterState = PrinterState Indent CurrentIndent

type Printer v = StateT PrinterState (Writer String) v

indent :: Printer Unit
indent = void $ modify $ \(PrinterState i ci) -> PrinterState i (ci + 1)

dedent :: Printer Unit
dedent = void $ modify $ \(PrinterState i ci) -> PrinterState i (ci - 1)

indentSpaces :: Printer String
indentSpaces = do
  (PrinterState indentWidth currentIndent) <- get
  pure $ fromCharArray $ replicate (indentWidth * currentIndent) ' '

appendLine :: String -> Printer Unit
appendLine "" = lift $ tell "\n"
appendLine s = do
  spaces <- indentSpaces
  lift $ tell $ spaces <> s <> "\n"

enclosed :: String -> String -> String -> String
enclosed before after contents = before <> contents <> after

openTag :: String -> Array XML.Attr -> String
openTag contents attrs = enclosed "<" ">" (contents <> showAttrs attrs)

closeTag :: String -> String
closeTag contents = enclosed "</" ">" contents

escape :: String -> String
escape s =
  case regex "[<>\t\n\r\"]" Flags.global of
    Left _ -> s
    Right exp -> replace' exp replacer s
  where replacer "<" _ = "&lt;"
        replacer ">" _ = "&gt;"
        replacer "\"" _ = "&quot;"
        replacer "\t" _ = ""
        replacer "\r" _ = ""
        replacer s' _ = s'

printNode :: XML.Node -> Printer Unit
printNode (XML.Comment s) = appendLine $ enclosed "<!-- " " -->" s
printNode (XML.Text s) = do
  sequence_ $ map appendLine $ split (Pattern "\n") $ escape s
printNode (XML.Element tagName attrs []) = do
  appendLine $ openTag tagName attrs <> closeTag tagName
printNode (XML.Element tagName attrs nodes) = do
  appendLine $ openTag tagName attrs
  indent
  sequence_ $ map printNode nodes
  dedent
  appendLine $ closeTag tagName

showAttrs :: Array XML.Attr -> String
showAttrs as = foldl iter "" as
  where iter acc (XML.Attr key value) = acc <> " " <> key <> "=\"" <> (escape value) <> "\""

printDocument :: XML.Document -> Printer Unit
printDocument (XML.Document version encoding node) = do
  appendLine $ "<?xml" <> (showAttrs [XML.Attr "version" version, XML.Attr "encoding" encoding]) <> "?>"
  printNode node

print :: Indent -> XML.Document -> String
print indentWidth doc =
  execWriter (runStateT (printDocument doc) (PrinterState indentWidth 0))
