module Data.Text.Format.Dodo.WrapRule where

import Prelude



import Prelude

import Data.Tuple.Nested ((/\), type (/\))
import Data.String (joinWith) as String
import Data.Array (foldl, intersperse, replicate) as Array

import Dodo as Dodo
import Dodo (text, space, break, enclose, foldWith, foldWithSeparator, lines, paragraph, indent) as DD
import Dodo.Internal (Doc(..)) as DD


type Markup a = Dodo.Doc a


data WrapRule a
    = Nil
    | Single (Markup a)
    | SurroundInline { left :: Markup a, right :: Markup a }
    | SurroundBlock { above :: Markup a, below :: Markup a }
    | Mark { marker :: Markup a }
    | HtmlTag { name :: String, attrs :: Array (String /\ String) }


applyStart :: forall a. WrapRule a -> Dodo.Doc a
applyStart = case _ of
    Nil -> DD.Empty
    Single markup -> markup
    SurroundInline { left } ->
        left
    SurroundBlock { above } ->
        above <> DD.break
    Mark { marker } ->
        marker
    HtmlTag { name, attrs } ->
        case attrs of
            [] -> DD.enclose (DD.text "<") (DD.text ">") $ DD.text name
            theAttrs ->
                DD.enclose
                    (DD.text "<" <> DD.text name <> DD.space)
                    (DD.text ">")
                    $ DD.foldWithSeparator
                        DD.space
                    $ ((\(attrName /\ attrValue) -> DD.text attrName <> DD.text "=" <> DD.enclose (DD.text "\"") (DD.text "\"") (DD.text attrValue))
                        <$> theAttrs)


applyEnd :: forall a. WrapRule a -> Dodo.Doc a
applyEnd = case _ of
    Nil -> DD.Empty
    Single _ -> DD.Empty
    SurroundInline { right } ->
        right
    SurroundBlock { below } ->
        DD.break <> below
    Mark _ ->
        DD.Empty
    HtmlTag { name } ->
        DD.enclose (DD.text "</") (DD.text ">") $ DD.text name