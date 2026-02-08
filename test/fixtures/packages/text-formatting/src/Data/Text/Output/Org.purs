module Data.Text.Output.Org where

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
    , ImageParams(..), ImageSide(..), QuoteOf(..), ChunkId(..), WrapKind(..)
    , bulletPrefix, hLevelToInt
    )
import Data.Text.Output (OutputKind, class Renderer, Support)
import Data.Text.Output (Support(..)) as S
import Data.Text.Output (layout) as O
import Data.Tuple (uncurry)
import Data.Tuple.Nested ((/\))
import Type.Proxy (Proxy(..))


foreign import data Org :: OutputKind


org = Proxy :: _ Org


layout :: Tag -> Doc
layout = O.layout org

-- FIXME: use Data.Text.Format.Org helpers
instance Renderer Org where

    supported :: Proxy Org -> Tag -> Support
    supported _ = case _ of
        _ -> S.Full -- FIXME

    layout :: Proxy Org -> Tag -> Doc
    layout = const $ case _ of
        Empty -> D.nil
        Plain str -> D.text str
        Newline -> D.break
        Format format tag ->
            case format of
                Fg _ -> layout tag
                Bg _ -> layout tag
                Header hLevel _ ->
                    D.repeat (hLevelToInt hLevel) (D.text "*") <> D.space <> layout tag -- TODO: use anchor
                Bold -> D.wrap "*" $ layout tag
                Emphasis -> D.wrap "/" $ layout tag
                Highlight -> D.wrap "==" $ layout tag
                Underline -> D.wrap "_" $ layout tag
                Strikethrough -> D.wrap "+" $ layout tag
                Monospaced -> D.wrap "~" $ layout tag
                Verbatim -> D.wrap "=" $ layout tag
                FixedWidth -> D.wrapbr "~" $ layout tag
                Code (ProgrammingLanguage lang) -> D.bracketbr ("#+BEGIN_SRC " <> lang) (layout tag) "#+END_SRC"
                Quote mbAuthor ->
                    D.bracketbr "#+BEGIN_QUOTE"
                        (layout tag <> case mbAuthor of
                            Just (QuoteOf author) -> D.text " -- " <> D.text author
                            Nothing -> D.nil
                        )
                    "#+END_QUOTE"
                Sub -> D.bracket "^_" (layout tag) "}"
                Sup -> D.bracket "^{" (layout tag) "}"
                Blink -> layout tag
                Inverse -> layout tag
                Invisible -> D.nil
                Define (Term dt) -> layout dt <> D.break <> D.mark ":" (layout tag)
                LinkTo (FootnoteId (E.Left ftn)) -> layout tag <> D.bracket "[^" (D.text $ show ftn) "]"
                LinkTo (FootnoteId (E.Right ftn)) -> layout tag <> D.bracket "[^" (D.text ftn) "]"
                Link (Url url) -> D.bracket "[" (D.bracket "[" (D.text url) "]" <> D.bracket "[" (layout tag) "]") "]"
                InlineImage _ _ -> D.text "" -- layout tag
                Comment -> D.bracketbr "#+BEGIN_COMMENT" (layout tag) "#+END_COMMENT"
                Footnote (FootnoteId (E.Left ftn)) -> D.bracket "[fn:" (D.text $ show ftn) "]" <> D.space <> layout tag
                Footnote (FootnoteId (E.Right ftn)) -> D.bracket "[fn:" (D.text ftn) "]" <> D.space <> layout tag
                -- _ -> layout tag -- other format's are not supported
        Split tagA tagB -> layout tagA <> D.text "|" <> layout tagB
        Align Left tag ->   {- D.mark "#+ALIGN_HTML:" (D.text "left") <> D.break <> -} layout tag
        Align Right tag ->  {- D.mark "#+ALIGN_HTML:" (D.text "right") <> D.break <> -} layout tag
        Align Center tag -> {- D.mark "#+ALIGN_HTML:" (D.text "center") <> D.break <> -} layout tag
        Pair tagA tagB -> layout tagA <> layout tagB
        Para tags -> D.stack $ layout <$> tags
        Nest (Indent i) tags -> D.nest' i $ layout <$> tags
        Join tag tags -> D.folddoc (<>) $ layout <$> Array.intersperse tag tags
        Wrap start end tag -> D.bracket' (layout start) (layout tag) (layout end) -- TODO: encode text
        Image (ImageParams params) (Url url) ->
            D.mark "#+CAPTION:" (D.text $ unwrap params.caption)  <> D.break <>
            (case params.width /\ params.height of
                Auto /\ Auto -> D.nil
                Px wpx /\ Px hpx ->
                    (htmlattr "width"  $ show wpx <> "px") <> D.break <>
                    (htmlattr "height" $ show hpx <> "px") <> D.break
                Px wpx /\ Auto -> (htmlattr "width" $ show wpx <> "px") <> D.break
                Auto /\ Px hpx -> (htmlattr "height" $ show hpx <> "px") <> D.break)
            <> D.bracket "[[" (D.text url) "]]"
        List bullet Empty items ->
            D.nest' 1 $ uncurry D.mark <$> b bullet <$> Array.mapWithIndex (/\) (layout <$> items)
        List bullet start items ->
            D.nest' 0 $ -- FIXME: support levels from `Nest`
                [ layout start
                , D.nest' 1 $ uncurry D.mark <$> b bullet <$> Array.mapWithIndex (/\) (layout <$> items)
                ]
        DefList definitions ->
            D.stack $ def <$> definitions
        Table headers rows ->
            D.nest' 0 $
                [ D.wrap "|" $ D.joinWith (D.text "|") $ layout <$> headers
                , D.wrap "|" $ D.join $ Array.intersperse (D.text "+") $ Array.replicate (Array.length headers) $ D.text "-"
                ] <> (D.wrap "|" <$> D.joinWith (D.text "|") <$> map layout <$> rows)
        Hr -> D.text "---------"
        Newpage -> D.break <> D.break
        Pagebreak _ -> D.break <> D.break
        WithId Block (ChunkId chunkId) tag -> D.mark "#+ID:" (D.text chunkId) <> D.break <> layout tag
        WithId _ _ tag -> layout tag
        WithClass _ _ tag -> layout tag -- FIXME
        Custom _ _ tag -> layout tag -- FIXME
        where
            b bullet (index /\ doc) = bulletPrefix index bullet /\ doc
            htmlattr attrName attrValue = D.mark "#+ATTR_HTML:" $ D.text (":" <> attrName) <> D.space <> D.text attrValue
            orgattr attrName attrValue = D.mark "#+ATTR_ORG:" $ D.text ":" <> D.text attrName <> D.space <> attrValue
            latexattr attrName attrValue = D.mark "#+ATTR_LATEX:" $ D.text ":" <> D.text attrName <> D.space <> attrValue
            def (TAndD (Term term /\ Definition def)) = D.mark (bulletPrefix 0 Dash) $ layout term <> D.text " :: " <> layout def