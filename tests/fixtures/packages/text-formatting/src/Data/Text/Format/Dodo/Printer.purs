module Data.Text.Format.Dodo.Printer where

import Prelude

import Debug as Debug

import Type.Proxy (Proxy(..))

import Data.List (List, (:))
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String (joinWith) as String
import Data.Tuple.Nested ((/\), type (/\))

import Data.Text.Output (OutputKind)
import Data.Text.Format.Dodo.Format (Directive) as F
import Data.Text.Format.Dodo.WrapRule as WR
import Data.Text.Format.Dodo.Renderer as DD
import Data.Text.Output.Markdown as Markdown

import Dodo (Printer(..), Doc, print, plainText, twoSpaces) as Dodo
import Dodo (text, break, indent) as DD
import Dodo.Internal (Doc(..)) as DD


type Buffer a = Dodo.Doc a


initBuffer :: forall a. Buffer a
initBuffer = DD.Empty

-- directiveRule :: forall content. (content -> S.Seam) -> X.Directive -> (content -> S.Seam)


withLast :: forall a. List a -> (a -> a) -> List a
withLast list f = fromMaybe list $ List.modifyAt (List.length list - 1) f list


printer :: forall (x :: OutputKind) a. DD.Renderer x => Proxy x -> Dodo.Printer (Buffer a) F.Directive (Dodo.Doc a)
printer pout = Dodo.Printer
    { emptyBuffer : initBuffer
    , enterAnnotation : \tag tags buff ->
        buff <> (WR.applyStart $ DD.render pout tag)
    , leaveAnnotation : \tag tags buff ->
        buff <> (WR.applyEnd   $ DD.render pout tag)
    , writeBreak : \buff ->
        buff <> DD.break
        -- buff { content = buff.content <> F.break }
    , writeIndent : \width str buff ->
        buff <> DD.indent (DD.text str)
    , writeText : \width str buff ->
        buff <> DD.text str
        -- buff { content = buff.content <> F.text str }
    -- , flushBuffer : Dodo.print Dodo.plainText Dodo.twoSpaces
    , flushBuffer : identity
    }


addDebugTrace :: forall buf ann res. Show buf => Dodo.Printer buf ann res -> Dodo.Printer buf ann res
addDebugTrace (Dodo.Printer printer) =
    Dodo.Printer
        { emptyBuffer : Debug.spy "init" printer.emptyBuffer
        , enterAnnotation : \tag tags buff ->
            let
                _ = Debug.spy "directive-enter: tag" tag
                -- _ = Debug.spy "directive-enter: tags" tags
                _ = Debug.spy "directive-enter: buff" $ show buff
                v = printer.enterAnnotation tag tags buff
                _ = Debug.spy "directive-enter: return" $ show v
                _ = Debug.spy "--------" "--------"
            in v
        , leaveAnnotation : \tag tags buff ->
            let
                _ = Debug.spy "directive-leave: tag" tag
                -- _ = Debug.spy "directive-leave: tags" tags
                _ = Debug.spy "directive-leave: buff" $ show buff
                v = printer.leaveAnnotation tag tags buff
                _ = Debug.spy "directive-leave: return" $ show v
                _ = Debug.spy "--------" "--------"
            in v
        , writeBreak : \buff ->
            let
                _ = Debug.spy "writeBreak: buff" $ show buff
                v = printer.writeBreak buff
                _ = Debug.spy "writeBreak: return" $ show v
                _ = Debug.spy "--------" "--------"
            in v
        , writeIndent : \width str buff ->
            let
                -- _ = Debug.spy "writeIndent: width" width
                _ = Debug.spy "writeIndent: str" str
                _ = Debug.spy "writeIndent: buff" $ show buff
                v = printer.writeIndent width str buff
                _ = Debug.spy "writeIndent: return" $ show v
                _ = Debug.spy "--------" "--------"
            in v
        , writeText : \width str buff ->
            let
                -- _ = Debug.spy "writeText: width" width
                _ = Debug.spy "writeText: str" str
                _ = Debug.spy "writeText: buff" $ show buff
                v = printer.writeText width str buff
                _ = Debug.spy "writeText: return" $ show v
                _ = Debug.spy "--------" "--------"
            in v
        , flushBuffer : \buff ->
            let
                _ = Debug.spy "flushBuffer: buff" $ show buff
                v = printer.flushBuffer buff
                _ = Debug.spy "flushBuffer: return" v
                _ = Debug.spy "--------" "--------"
            in v
        }