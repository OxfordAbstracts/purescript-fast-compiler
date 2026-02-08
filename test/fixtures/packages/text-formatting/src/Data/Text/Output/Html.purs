module Data.Text.Output.Html where

import Prelude

import Color as Color

import Type.Proxy (Proxy(..))

import Data.Array (intersperse) as Array
import Data.Newtype (unwrap)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..)) as E
import Data.Tuple.Nested ((/\))
import Data.Text.Format
    ( Tag(..), Format(..), Align(..), Term(..), Definition(..), TermAndDefinition(..)
    , Url(..), HLevel(..), Anchor(..), FootnoteId(..), ProgrammingLanguage(..), Bullet(..)
    , Indent(..), ImageParams(..), ImageSide(..), QuoteOf(..), ChunkId(..), ChunkClass(..)
    , WrapKind(..)
    )
import Data.Text.Output (layout) as O
import Data.Text.Output (OutputKind, class Renderer, Support)
import Data.Text.Output (Support(..)) as S
import Data.Text.Doc (Doc)
import Data.Text.Doc as D


foreign import data Html :: OutputKind


html = Proxy :: _ Html


layout :: Tag -> Doc
layout = O.layout html


instance Renderer Html where

    supported :: Proxy Html -> Tag -> Support
    supported _ = case _ of
        Empty -> S.Full
        Plain _ -> S.Full
        Newline -> S.Full
        Format format _ ->
            case format of
                Fg _ -> S.Full
                Bg _ -> S.Full
                Bold -> S.Full
                Underline -> S.Full
                Blink -> S.Full
                Inverse -> S.Full
                Invisible -> S.Full
                Define _ -> S.Text
                Link _ -> S.Partly
                InlineImage _ _ -> S.Partly
                LinkTo _ -> S.Partly
                Comment -> S.Text
                _ -> S.Text -- TODO
        Split _ _ -> S.Partly
        Align _ _ -> S.Full
        Pair _ _ -> S.Full
        Para _ -> S.Full
        Nest _ _ -> S.Full
        Join _ _ -> S.Full
        Wrap _ _ _ -> S.Full
        List _ _ _ -> S.Full
        DefList _ -> S.Full
        Image _ _ -> S.Full
        Table _ _ -> S.None
        Hr -> S.Text
        Newpage -> S.None
        Pagebreak _ -> S.None
        WithId _ _ _ -> S.Full
        WithClass _ _ _ -> S.Full
        Custom _ _ _ -> S.Full

    layout :: Proxy Html -> Tag -> Doc
    layout = const $ case _ of
        Empty -> D.nil
        Plain str -> D.text str
        Newline -> D.bracket "<" (D.text "br") "/>"
        Format format tag ->
            case format of
                Fg (E.Left colorStr) -> wrapS "span" ("color:" <> colorStr) tag
                Fg (E.Right color) -> wrapS "span" ("color:" <> Color.toHexString color) tag
                Bg (E.Left colorStr) -> wrapS "span" ("background-color:" <> colorStr) tag
                Bg (E.Right color) -> wrapS "span" ("background-color:" <> Color.toHexString color) tag
                Header hLevel mbAnchor -> wrap' (hLevelTag hLevel) $ case mbAnchor of
                    Just (Anchor anchor) -> wrapAttr "a" "name" anchor tag
                    Nothing -> layout tag
                Bold -> wrap "b" tag
                Emphasis -> wrap "em" tag
                Underline -> wrap "ins" tag
                Strikethrough -> wrap "del" tag
                Monospaced -> wrap "code" tag
                Verbatim -> wrap "code" tag
                FixedWidth -> wrap "code" tag
                Highlight -> wrap "mark" tag
                Code (ProgrammingLanguage lang) -> wrapAttr "code" "lang" lang tag
                Quote mbAuthor ->
                    case mbAuthor of
                        Just (QuoteOf author) -> wrapAttr "quote" "cite" author tag
                        Nothing -> wrap "qoute" tag
                Sub -> wrap "sub" tag
                Sup -> wrap "sup" tag
                Blink -> wrap "blink" tag
                Inverse -> wrap "inverse" tag
                Invisible -> wrapS "span" "display:none" tag
                Define (Term dt) -> let dd = tag in wrap "dd" dd <> wrap "dt" dt
                LinkTo (FootnoteId (E.Left ftn)) -> wrapAttr "a" "href" ("#" <> show ftn) tag
                LinkTo (FootnoteId (E.Right ftn)) -> wrapAttr "a" "href" ("#" <> ftn) tag
                Link (Url url) -> wrapAttr "a" "href" url tag
                InlineImage (ImageParams params) (Url url) ->
                    case params.width /\ params.height of
                        Auto /\ Auto ->     wrapAttrsE "img" [ "src" /\ url, "alt" /\ unwrap params.caption, inlineBlockStyle ] tag
                        Px wpx /\ Px hpx -> wrapAttrsE "img" [ "src" /\ url, "width" /\ show wpx, "height" /\ show hpx, "alt" /\ unwrap params.caption, inlineBlockStyle ] tag
                        Px wpx /\ Auto ->   wrapAttrsE "img" [ "src" /\ url, "width" /\ show wpx, "height" /\ "auto", "alt" /\ unwrap params.caption, inlineBlockStyle ] tag
                        Auto /\ Px hpx ->   wrapAttrsE "img" [ "src" /\ url, "width" /\ "auto", "height" /\ show hpx, "alt" /\ unwrap params.caption, inlineBlockStyle ] tag
                Comment -> D.bracket "<!--" (layout tag) "-->"
                Footnote (FootnoteId (E.Left ftn)) -> wrapAttr "a" "name" ("#" <> show ftn) tag
                Footnote (FootnoteId (E.Right ftn)) -> wrapAttr "a" "name" ("#" <> ftn) tag
                -- _ -> layout tag -- other format's are not supported
        Split tagA tagB -> layout tagA <> layout tagB
        Align Left tag -> wrapS "div" "text-align:left" tag
        Align Right tag -> wrapS "div" "text-align:right" tag
        Align Center tag -> wrapS "div" "text-align:center" tag
        Pair tagA tagB -> layout tagA <> layout tagB
        Para tags -> D.stack $ layout <$> tags
        Nest i tags -> D.nest' (unwrap i) $ indent i <$> tags
        Join tag tags -> D.folddoc (<>) $ layout <$> Array.intersperse tag tags
        Wrap start end tag -> D.bracket' (layout start) (layout tag) (layout end) -- TODO: encode text
        List bullet Empty items ->
            wrapS' "ul" ("list-style-type:" <> case bullet of
                Asterisk -> "bullet"
                Alpha -> "lower-alpha"
                AlphaInv -> "none" -- FIXME
                Disc -> "disc"
                Circle -> "circle"
                Dash -> "'- '" -- "dash"
                Num -> "decimal"
                None -> "none"
                BCustom str -> "'" <> str <> "'"
            ) $ D.stack $ wrap "li" <$> items
        Image (ImageParams params) (Url url) ->
            case params.width /\ params.height of
                Auto /\ Auto ->     wrapAttrsE' "img" [ "src" /\ url, "alt" /\ unwrap params.caption ]
                Px wpx /\ Px hpx -> wrapAttrsE' "img" [ "src" /\ url, "width" /\ show wpx, "height" /\ show hpx, "alt" /\ unwrap params.caption ]
                Px wpx /\ Auto ->   wrapAttrsE' "img" [ "src" /\ url, "width" /\ show wpx, "height" /\ "auto", "alt" /\ unwrap params.caption ]
                Auto /\ Px hpx ->   wrapAttrsE' "img" [ "src" /\ url, "width" /\ "auto", "height" /\ show hpx, "alt" /\ unwrap params.caption ]
        List bullet start items ->
            wrapAttr "label" "for" "" start
            <> layout (List bullet Empty items)
        DefList definitions ->
            wrap' "dl" $ D.stack $ def <$> definitions
        Table headers rows ->
            wrap' "table"
                $ (wrap' "thead" $ D.stack $ wrap "th" <$> headers)
                <> D.break <> D.stack (wrap' "tr" <$> D.stack <$> map (wrap "td") <$> rows)
        Hr -> wrapE "hr"
        Newpage -> D.break <> D.break
        Pagebreak _ -> D.break <> D.break
        WithId wk (ChunkId chId) tag -> wrapAttr (tagByWrapKind wk) "id" chId tag
        WithClass wk (ChunkClass chClass) tag -> wrapAttr (tagByWrapKind wk) "class" chClass tag
        Custom name attrs tag -> wrapAttrsE name attrs tag
        where
            -- b bullet (index /\ doc) = bulletPrefix index bullet /\ doc
            indent (Indent n) = wrapS "div" ("margin-left:" <> show (n * 8) <> "px")
            inlineBlockStyle = "style" /\ "display:inline-block"
            wrap htmlTag = wrap' htmlTag <<< layout
            wrap' htmlTag content = D.bracket "<" (D.text htmlTag) ">" <> content <> D.bracket "</" (D.text htmlTag) ">"
            wrapAttr htmlTag attrName attrVal = wrapAttr' htmlTag attrName attrVal <<< layout
            wrapAttr' htmlTag attrName attrVal content = D.bracket "<" (D.text htmlTag <> D.space <> makeAttr (attrName /\ attrVal)) ">" <> content <> D.bracket "</" (D.text htmlTag) ">" -- TODO: wrapAttrs Array.singleton
            wrapAttrs htmlTag attrs = wrapAttrs' htmlTag attrs <<< layout
            wrapAttrs' htmlTag attrs content = D.bracket "<" (D.text htmlTag <> D.space <> D.joinWith D.space (makeAttr <$> attrs)) ">" <> content <> D.bracket "</" (D.text htmlTag) ">"
            makeAttr (attrName /\ attrVal) = D.text (attrName <> "=") <> D.wrap "\"" (D.text attrVal)
            wrapAttrsE htmlTag attrs content = wrapAttrsE' htmlTag attrs <> layout content
            wrapAttrsE' htmlTag attrs = D.bracket "<" (D.text htmlTag <> D.space <> D.joinWith D.space (makeAttr <$> attrs)) "/>"
            wrapS htmlTag = wrapAttr htmlTag "style"
            wrapS' htmlTag = wrapAttr' htmlTag "style"
            wrapE htmlTag = D.bracket "<" (D.text htmlTag) "/>"
            def (TAndD (Term term /\ Definition definition)) = wrap' "dt" (layout term) <> D.break <> wrap' "dd" (layout definition)
            tagByWrapKind Block = "div"
            tagByWrapKind Inline = "span"



singleLine :: Tag -> String
singleLine = layout >>> D.render { break : D.Space, indent : D.Empty }
-- render = S.perform blessed { break : D.Space, indent : D.Empty }


multiLine :: Tag -> String
multiLine = layout >>> D.render { break : D.All, indent : D.Spaces 2 }


hLevelTag :: HLevel -> String
hLevelTag = case _ of
    H1 -> "h1"
    H2 -> "h2"
    H3 -> "h3"
    H4 -> "h4"
    H5 -> "h5"
    H6 -> "h6"