module Data.Text.Output.Blessed where

import Prelude

import Color as Color

import Type.Proxy (Proxy(..))

import Data.Array (intersperse, mapWithIndex) as Array
import Data.Newtype (unwrap) as NT
import Data.Maybe (fromMaybe)
import Data.Enum (toEnum)
import Data.Either (Either(..)) as E
import Data.Tuple (curry, uncurry)
import Data.Tuple.Nested ((/\), type (/\))
import Data.String (joinWith) as String
import Data.Text.Format (Tag(..), Format(..), Align(..), Term(..), Definition(..), TermAndDefinition(..), Url(..), HLevel(..), Anchor(..), FootnoteId(..), ProgrammingLanguage(..), Indent(..), Bullet(..), ImageParams(..), bulletPrefix)
import Data.Text.Output (OutputKind, class Renderer, Support)
import Data.Text.Output (layout) as O
import Data.Text.Output (Support(..), perform) as S
import Data.Text.Doc (Doc, (<+>))
import Data.Text.Doc as D
import Data.DateTime (DateTime(..)) as DT
import Data.DateTime as DateTime
import Data.Date (Date(..), canonicalDate) as Dt
import Data.Date as Date
import Data.Time (Time(..)) as Tm
import Data.Time.Component (Hour(..), Minute(..), Millisecond(..)) as Tm
import Data.Time as Time
import Data.Formatter.DateTime as FDT
import Data.Newtype (unwrap)

foreign import data Blessed :: OutputKind


blessed = Proxy :: _ Blessed


layout :: Tag -> Doc
layout = O.layout blessed


instance Renderer Blessed where

    supported :: Proxy Blessed -> Tag -> Support
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
                InlineImage _ _ -> S.Text
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
        List _ _ _ -> S.Text
        Image _ _ -> S.Text
        DefList _ -> S.Text
        Table _ _ -> S.None
        Hr -> S.Text
        Newpage -> S.None
        Pagebreak _ -> S.None
        WithId _ _ _ -> S.Partly
        WithClass _ _ _ -> S.Partly
        Custom _ _ _ -> S.Partly

    layout :: Proxy Blessed -> Tag -> Doc
    layout = const $ case _ of
        Empty -> D.nil
        Plain str -> D.text str
        Newline -> D.break
        Format format tag ->
            case format of
                Fg (E.Left colorStr) -> wrap (colorStr <> "-fg") tag
                Fg (E.Right color) -> wrap (Color.toHexString color <> "-fg") tag
                Bg (E.Left colorStr) -> wrap (colorStr <> "-bg") tag
                Bg (E.Right color) -> wrap (Color.toHexString color <> "-bg") tag
                Bold -> wrap "bold" tag
                Underline -> wrap "underline" tag
                Blink -> wrap "blink" tag
                Inverse -> wrap "inverse" tag
                Invisible -> wrap "invisible" tag
                Define (Term dt) -> let dd = tag in D.break <> layout dt <+> D.text "::" <+> layout dd <> D.break
                LinkTo ftn -> layout tag <+> D.bracket "[" (D.text $ show $ NT.unwrap ftn) "]"
                Link (Url url) -> let title = tag in layout title <+> D.bracket "(" (D.text url) ")"
                InlineImage (ImageParams { caption }) (Url url) -> let title = tag in layout title <+> D.bracket "(" (ifnec caption <> D.text url) ")"
                Comment -> D.break <> layout tag
                _ -> layout tag -- other format's are not supported
        Split tagA tagB -> layout tagA <> D.text "{|}" <> layout tagB
        Align Left tag -> wrap "left" tag
        Align Right tag -> wrap "right" tag
        Align Center tag -> wrap "center" tag
        Pair tagA tagB -> layout tagA <> layout tagB
        Para tags -> D.stack $ layout <$> tags
        Nest i tags -> D.nest' (NT.unwrap i) $ layout <$> tags
        Join tag tags -> D.folddoc (<>) $ layout <$> Array.intersperse tag tags
        Wrap start end tag -> D.bracket' (layout start) (layout tag) (layout end) -- TODO: encode text
        Image (ImageParams { caption }) (Url url) -> D.nest 0 $
            if unwrap caption == "" then
                D.bracket "[[" (D.text url) "]]"
            else
                D.bracket "[[" (D.text url) "]]" <> D.bracket "(" (D.text $ unwrap caption) ")"
        List bullet Empty items ->
            D.nest' 1 $ uncurry D.mark <$> b bullet <$> Array.mapWithIndex (/\) (layout <$> items)
        List bullet start items ->
            D.nest' 0 $ -- FIXME: support levels from `Nest`
                [ layout start
                , D.nest' 1 $ uncurry D.mark <$> b bullet <$> Array.mapWithIndex (/\) (layout <$> items)
                ]
        DefList items ->
            D.stack $ def <$> items
        Table headers rows ->
            D.nest' 0 $
                [ D.joinWith (D.text "|") $ layout <$> headers
                , layout Hr
                ] <> (D.joinWith (D.text "|") <$> map layout <$> rows)

        Hr -> D.text "----------"
        Newpage -> D.break <> D.break
        Pagebreak _ -> D.break <> D.break
        WithId _ _ tag -> layout tag
        WithClass _ _ tag -> layout tag
        Custom _ _ tag -> layout tag
        where
            b bullet (index /\ doc) = bulletPrefix index bullet /\ doc
            wrap cmd tag = D.bracket "{" (D.text cmd) "}" <> layout tag <> D.bracket "{/" (D.text cmd) "}"
            def (TAndD (Term term /\ Definition def)) = layout term <> D.text " :: " <> layout def
            ifnec caption = if unwrap caption == "" then D.text "" else (D.text $ unwrap caption) <> D.text ","


singleLine :: Tag -> String
singleLine = layout >>> D.render { break : D.Space, indent : D.Empty }
-- render = S.perform blessed { break : D.Space, indent : D.Empty }


multiLine :: Tag -> String
multiLine = layout >>> D.render { break : D.All, indent : D.Spaces 2 }