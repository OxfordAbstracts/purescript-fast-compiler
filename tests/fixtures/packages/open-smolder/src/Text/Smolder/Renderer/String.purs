module Text.Smolder.Renderer.String
  ( render
  , render'
  , renderWithOptions
  , noPP
  , twoSpacesPP
  ) where

import Prelude

import Control.Comonad (extend)
import Control.Comonad.Cofree (Cofree, head, mkCofree, tail, (:<))
import Control.Monad.Free (foldFree)
import Control.Monad.State (State, evalState, execState, get, put, state)
import Data.Array ((..))
import Data.Array as Array
import Data.CatList (CatList)
import Data.CatList as CatList
import Data.Char (toCharCode)
import Data.Foldable (elem, fold, foldr)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.String.CodeUnits (fromCharArray, toCharArray)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import JSURI (encodeURI)
import Partial (crashWith)
import Partial.Unsafe (unsafePartial)
import Text.Smolder.Markup (Attr(..), Markup, MarkupM(..), NS(..))

escapeMap :: Map Char String
escapeMap = Map.fromFoldable
  [ '&' /\ "&amp;"
  , '<' /\ "&lt;"
  , '>' /\ "&gt;"
  , '"' /\ "&quot;"
  , '\'' /\ "&#39;"
  , '/' /\ "&#x2F;"
  ]

escapeMIMEMap :: Map Char String
escapeMIMEMap = Map.fromFoldable
  [ '&' /\ "&amp;"
  , '<' /\ "&lt;"
  , '"' /\ "&quot;"
  , '\'' /\ "&#39;"
  ]

voidElements :: Set String
voidElements = Set.fromFoldable
  [ "area"
  , "base"
  , "br"
  , "col"
  , "command"
  , "embed"
  , "hr"
  , "img"
  , "input"
  , "keygen"
  , "link"
  , "meta"
  , "param"
  , "source"
  , "track"
  , "wbr"
  ]

isMIMEAttr :: String -> String -> Boolean
isMIMEAttr tag attr
  | attr == "type" && tag == "embed" = true
  | attr == "type" && tag == "object" = true
  | attr == "type" && tag == "script" = true
  | attr == "type" && tag == "source" = true
  | attr == "type" && tag == "style" = true
  | otherwise = false

-- url attributes according to:
-- https://developer.mozilla.org/en-US/docs/Web/HTML/Attributes
isURLAttr :: String -> String -> Boolean
isURLAttr tag attr
  | attr == "href" && tag == "a" = true
  | attr == "href" && tag == "area" = true
  | attr == "href" && tag == "base" = true
  | attr == "href" && tag == "link" = true
  | attr == "src" && tag == "audio" = true
  | attr == "src" && tag == "embed" = true
  | attr == "src" && tag == "iframe" = true
  | attr == "src" && tag == "img" = true
  | attr == "src" && tag == "input" = true
  | attr == "src" && tag == "script" = true
  | attr == "src" && tag == "source" = true
  | attr == "src" && tag == "track" = true
  | attr == "src" && tag == "video" = true
  | attr == "code" && tag == "applet" = true
  | attr == "codebase" && tag == "applet" = true
  | attr == "data" && tag == "object" = true
  | attr == "manifest" && tag == "html" = true
  | attr == "poster" && tag == "video" = true
  | otherwise = false

toStream :: String -> Cofree Maybe Char
toStream s = foldr (\c t -> c :< (Just t)) (mkCofree '\x0' Nothing) cs
  where
  cs = toCharArray s

fromStream :: Cofree Maybe String -> String
fromStream = go ""
  where
  go :: String -> Cofree Maybe String -> String
  go result cof =
    case (head cof), (tail cof) of
      _, Nothing -> result
      s, (Just cof') -> go (result <> s) cof'

escape :: Map Char String -> String -> String
escape m = fromStream <<< extend escapeS <<< toStream
  where
  startsEntity :: Maybe (Cofree Maybe Char) -> Boolean
  startsEntity (Just w) =
    case head w, tail w of
      '#', Just w' -> checkTail (48 .. 57) w'
      '#', Nothing -> false
      _, _ -> checkTail (65 .. 90 <> 97 .. 122) w
  startsEntity Nothing = false

  checkTail :: Array Int -> Cofree Maybe Char -> Boolean
  checkTail allowed = flip evalState false <<< checkTail'
    where
    -- keep if `;` is allowed in `State` monad
    checkTail' :: Cofree Maybe Char -> State Boolean Boolean
    checkTail' w =
      case toCharCode $ head w of
        cc
          | cc `elem` allowed -> do
              put true
              fromMaybe (pure false) $ checkTail' <$> tail w
          | cc == 59 -> get
          | otherwise -> pure false

  escapeS :: Cofree Maybe Char -> String
  escapeS w =
    case head w of
      '&'
        | startsEntity (tail w) -> "&"
        | otherwise -> "&amp;"
      c -> fromMaybe (fromCharArray [ c ]) $ Map.lookup c m

escapeAttrValue :: String -> String -> String -> String
escapeAttrValue tag key value
  | isURLAttr tag key =
      case encodeURI value of
        Nothing -> unsafePartial $ crashWith "Text.Smolder.Renderer.String.escapeAttrValue: cannot encode URL"
        Just x -> x
  | isMIMEAttr tag key = escape escapeMIMEMap value
  | otherwise = escape escapeMap value

showAttrs :: String -> CatList Attr → String
showAttrs tag = map showAttr >>> fold
  where
  showAttr (SafeAttr key value) = " " <> key <> "=\"" <> value <> "\""
  showAttr (Attr key value) = " "
    <> key
    <> "=\""
    <> escapeAttrValue tag key value
    <> "\""

renderItem :: ∀ e. PPOptions -> MarkupM e ~> State (CatList String)
renderItem ppoptions (Element ns name children attrs _ rest) =
  let
    indentedOpen = indent ppoptions.depth ppoptions.indentStr ("<" <> name <> showAttrs name attrs)
    c = renderWithOptions (ppoptions { depth = ppoptions.depth + 1 }) children
    hasChildren = CatList.length c > 0 || (ns == HTMLns && not (Set.member name voidElements))
    b =
      if hasChildren then
        let
          end = "</" <> name <> ">"
        in
          if CatList.length c > 0 then CatList.singleton (indentedOpen <> ">") <> c <> CatList.singleton (indent ppoptions.depth ppoptions.indentStr end)
          else CatList.singleton (indentedOpen <> ">" <> end)
      else CatList.singleton (indentedOpen <> "/>")
  in
    state \s → Tuple rest $ append s b
renderItem ppoptions (Content text rest) = state \s →
  let
    indentedText =
      if String.length ppoptions.indentStr > 0 then
        if String.length text > 0 then CatList.singleton $ indent ppoptions.depth ppoptions.indentStr (escape escapeMap text)
        else CatList.empty
      else CatList.singleton $ escape escapeMap text
  in
    Tuple rest $ append s indentedText
renderItem ppoptions (Doctype text rest) = state \s →
  let
    indentedDoctype = indent ppoptions.depth ppoptions.indentStr ("<!DOCTYPE " <> text <> ">")
  in
    Tuple rest $ append s (CatList.singleton indentedDoctype)
renderItem _ (Empty rest) = pure rest

-- | Render markup as an HTML string with pretty printing options.
renderWithOptions :: ∀ e. PPOptions -> Markup e → CatList String
renderWithOptions ppoptions f = execState (foldFree (renderItem ppoptions) f) CatList.empty

-- | Render markup as an HTML string with no pretty printing.
render' :: ∀ e. PPOptions -> Markup e → String
render' ppoptions markup = String.joinWith ppoptions.newline $ Array.fromFoldable $ renderWithOptions ppoptions markup

-- render' ppoptions markup =
--   let catList = renderWithOptions ppoptions markup
--       -- Use foldl to accumulate the string, without adding a newline to the last element
--       accumulatedString = foldl (\(Tuple acc isFirst) line ->
--                                   let newAcc = acc <> (if isFirst then "" else ppoptions.newline) <> line
--                                   in (Tuple newAcc false)) (Tuple "" true) catList
--   in fst accumulatedString

render :: ∀ e. Markup e → String
render = render' noPP

type PPOptions =
  { indentStr :: String
  , newline :: String
  , depth :: Int -- Tracks the current depth for indentation
  }

-- Define a version of PPOptions without pretty printing
noPP :: PPOptions
noPP = { indentStr: "", newline: "", depth: 0 }

-- Define a version of PPOptions with two spaces for indentation and newline
twoSpacesPP :: PPOptions
twoSpacesPP = { indentStr: "  ", newline: "\n", depth: 0 }

indent :: Int -> String -> String -> String
indent n indentation s = indentWithoutTrim n indentation (String.trim s)

indentWithoutTrim :: Int -> String -> String -> String
indentWithoutTrim 0 _ s = s
indentWithoutTrim _ _ "" = ""
indentWithoutTrim n indentation s = prefix <> s
  where
  prefix = String.joinWith "" (Array.replicate n indentation)
