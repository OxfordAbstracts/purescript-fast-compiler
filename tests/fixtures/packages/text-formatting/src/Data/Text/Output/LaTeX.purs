module Data.Text.Output.LaTeX where

import Prelude

import Color as Color

import Data.Array (length, replicate, intersperse, mapWithIndex) as Array
import Data.Either (Either(..)) as E
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Text.Doc (Doc)
import Data.Text.Doc as D
import Data.Text.Format
    ( Tag(..), Format(..), Align(..), Term(..), Definition(..), Url(..), HLevel(..), Anchor(..)
    , FootnoteId(..), ProgrammingLanguage(..), Indent(..), TermAndDefinition(..), Bullet(..)
    , ImageParams(..), ImageSide(..), QuoteOf(..)
    , bulletPrefix
    )
import Data.Text.Output (OutputKind, class Renderer, Support)
import Data.Text.Output (Support(..)) as S
import Data.Text.Output (layout) as O
import Data.Tuple (uncurry)
import Data.Tuple.Nested ((/\))
import Data.String (toLower) as String

import Type.Proxy (Proxy(..))


foreign import data LaTeX :: OutputKind


latex = Proxy :: _ LaTeX


layout :: Tag -> Doc
layout = O.layout latex


-- FIXME: use Data.Text.Format.Latex helpers
instance Renderer LaTeX where

    supported :: Proxy LaTeX -> Tag -> Support
    supported _ = case _ of
        _ -> S.Full -- FIXME

    -- packages: xcolor, minted, epigraph, csquotes

    layout :: Proxy LaTeX -> Tag -> Doc
    layout = const $ case _ of
        Empty -> D.nil
        Plain str -> D.text str
        Newline -> D.break
        Format format tag ->
            case format of
                Fg (E.Left colorStr) -> latexCmdAttr "textcolor" colorStr tag
                Fg (E.Right colorVal) -> latexCmdAttr "textcolor" ("#" <> Color.toHexString colorVal) tag
                Bg (E.Left colorStr) -> latexCmdAttr "colorbox" colorStr tag
                Bg (E.Right colorVal) -> latexCmdAttr "colorbox" ("#" <> Color.toHexString colorVal) tag
                Header hLevel _ -> latexCmd (hLevelCmd Article hLevel) tag -- https://www.overleaf.com/learn/latex/Sections_and_chapters#Document_sectioning
                Bold -> latexCmd "textbf" tag
                Emphasis -> latexCmd "emph" tag
                Highlight -> latexCmd "hl" tag
                Underline -> latexCmd "underline" tag
                Strikethrough -> latexCmd "sout" tag
                Monospaced -> latexCmd "texttt" tag
                Verbatim -> latexCmd "varb" tag -- latexBeginEnd "verbatim" tag
                FixedWidth -> layout tag -- TODO: ?
                Code (ProgrammingLanguage lang) ->
                    latexBeginEndAttr "minted" (String.toLower lang) tag
                Quote mbAuthor ->
                    case mbAuthor of
                        Just (QuoteOf author) -> latexCmd' "displayquote" (layout tag <> D.space <> D.text "--" <> D.space <> D.text author)
                        Nothing -> latexBeginEnd "displayquote" tag
                Sub -> D.text "_" <> D.bracket "{" (layout tag) "}"
                Sup -> D.text "^" <> D.bracket "{" (layout tag) "}"
                Blink -> layout tag
                Inverse -> layout tag -- TODO
                Invisible -> D.nil  -- TODO
                Define (Term dt) -> latexCmdAttrSq' "item" (layout dt) tag -- latexListItem (Just dt) $ layout tag
                Footnote (FootnoteId (E.Left ftn)) -> latexCmdAttrSq "footnote" (show ftn) tag
                Footnote (FootnoteId (E.Right ftn)) -> latexCmdAttrSq "footnote" ftn tag
                LinkTo (FootnoteId (E.Left ftn)) -> layout tag <> latexCmdAttrSqE "footnotemark" (show ftn)
                LinkTo (FootnoteId (E.Right ftn)) -> layout tag <> latexCmdAttrSqE "footnotemark" ftn
                Link (Url url) -> latexCmdAttr "href" url tag
                InlineImage _ _ -> layout tag -- TODO
                Comment -> D.nil -- TODO
                -- _ -> layout tag -- other format's are not supported
        Split tagA tagB -> layout tagA <> D.text "|" <> layout tagB
        Pair tagA tagB -> layout tagA <> layout tagB
        Para tags -> D.stack $ layout <$> tags
        Nest (Indent i) tags -> D.nest' i $ layout <$> tags
        Join tag tags -> D.folddoc (<>) $ layout <$> Array.intersperse tag tags
        Wrap start end tag -> D.bracket' (layout start) (layout tag) (layout end) -- TODO: encode text

        Align Left tag ->   latexBeginEnd "raggedleft" tag -- latexCmd / switch?
        Align Right tag ->  latexBeginEnd "raggedright" tag -- latexCmd / switch?
        Align Center tag -> latexBeginEnd "center" tag
        Image (ImageParams params) (Url url) ->
            case params.width /\ params.height of
                Auto /\ Auto -> latexCmd "includegraphics" $ Plain url
                Px wpx /\ Px hpx ->
                    latexCmdAttrSq2 "includegraphics" ("width=" <> show wpx <> "pt") ("height=" <> show hpx <> "pt") $ Plain url
                Px wpx /\ Auto ->
                    latexCmdAttrSq "includegraphics" ("width=" <> show wpx <> "pt") $ Plain url
                Auto /\ Px hpx ->
                    latexCmdAttrSq "includegraphics" ("height=" <> show hpx <> "pt") $ Plain url
        List bullet Empty items ->
            latexBeginEndNls' "itemize" $
                D.nest' 1 $ uncurry latexListItem <$> b bullet <$> Array.mapWithIndex (/\) (layout <$> items)
        List bullet start items ->
            D.nest' 0 $ -- FIXME: support levels from `Nest`
                [ layout start
                , latexBeginEndNls' "itemize" $
                    D.nest' 1 $ uncurry latexListItem <$> b bullet <$> Array.mapWithIndex (/\) (layout <$> items)
                ]
        DefList definitions ->
            latexBeginEndNls' "itemize" $ D.stack $ def <$> definitions
        Table headers rows ->
            -- https://www.overleaf.com/learn/latex/Tables
            -- FIXME: implement
            D.nil
        Hr -> D.text "\\hline"
        Newpage -> D.text "\\newpage"
        Pagebreak mbPriority -> case mbPriority of
            Just priority -> D.text "\\pagebreak" <> D.space <> D.text (show priority)
            Nothing -> D.text "\\pagebreak"
        WithId _ _ tag -> layout tag -- FIXME
        WithClass _ _ tag -> layout tag -- FIXME
        Custom _ _ tag -> layout tag -- FIXME
        where
            latexCmd cmd tag = latexCmd' cmd $ layout tag
            latexCmd' cmd doc = D.bracket ("\\" <> cmd <> "{") doc "}"
            latexCmdAttr cmd attrVal tag = D.bracket ("\\" <> cmd <> "{") (D.text attrVal) "}" <> D.bracket "{" (layout tag) "}"
            latexCmdAttrSq cmd attrVal tag = D.bracket ("\\" <> cmd <> "[") (D.text attrVal) "]" <> D.bracket "{" (layout tag) "}"
            latexCmdAttrSq' cmd attrVal tag = D.bracket ("\\" <> cmd <> "[") attrVal "]" <> layout tag
            latexCmdAttrSq2 cmd attr1Val attr2Val tag = D.bracket ("\\" <> cmd <> "[") (D.text attr1Val <> D.text "," <> D.space <> D.text attr2Val) "]" <> D.bracket "{" (layout tag) "}"
            latexCmdAttrSqE cmd attrVal = D.bracket ("\\" <> cmd <> "[") (D.text attrVal) "]"
            latexBeginEnd cmd tag = latexBeginEnd' cmd $ layout tag
            latexBeginEnd' cmd doc = (latexCmd "begin" $ Plain cmd) <> doc <> (latexCmd "end" $ Plain cmd)
            latexBeginEndAttr cmd attrVal tag = (latexCmd "begin" $ Plain cmd) <> D.bracket "{" (D.text attrVal) "}" <> layout tag <> (latexCmd "end" $ Plain cmd)
            latexBeginEndNls cmd tag = latexBeginEndNls' cmd $ layout tag
            latexBeginEndNls' cmd doc = (latexCmd "begin" $ Plain cmd) <> D.break <> doc <> D.break <> (latexCmd "end" $ Plain cmd)
            latexBeginEndNlsAttr cmd attrVal tag = (latexCmd "begin" $ Plain cmd) <> D.break <> D.bracket "{" (D.text attrVal) "}" <> layout tag <> D.break <> (latexCmd "end" $ Plain cmd)
            latexListItem Nothing doc = D.text "\\item" <> D.space <> doc
            latexListItem (Just bulletStr) doc = (D.text $ "\\item[" <> bulletStr <> "]") <> D.space <> doc
            b bullet (index /\ doc) = case bullet of
                None -> Nothing /\ doc
                _ -> (Just $ bulletPrefix index bullet) /\ doc
            def (TAndD (Term term /\ Definition definition)) = latexCmdAttrSq' "item" (layout term) definition -- latexListItem (Just dt) $ layout tag


data DocumentClass
    = Article
    | Book


hLevelCmd :: DocumentClass -> HLevel -> String
hLevelCmd docClass hLevel =
    -- https://www.overleaf.com/learn/latex/Sections_and_chapters#Document_sectioning
    case docClass of
        Book ->
            case hLevel of
                H1 -> "part"
                H2 -> "chapter"
                H3 -> "section"
                H4 -> "subsection"
                H5 -> "subsubsection"
                H6 -> "paragraph"
        Article ->
            case hLevel of
                H1 -> "part"
                H2 -> "section"
                H3 -> "subsection"
                H4 -> "subsubsection"
                H5 -> "paragraph"
                H6 -> "subparagraph"