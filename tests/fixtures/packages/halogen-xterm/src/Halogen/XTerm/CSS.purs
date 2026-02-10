module Halogen.XTerm.CSS where

import Prelude hiding (top, bottom)

import CSS (CSS, absolute, backgroundColor, black, block, bottom, byClass, color, cursor, display, displayNone, element, em, fromString, height, inlineBlock, key, left, lineThrough, margin, opacity, overline, padding, position, prefixed, pseudo, px, relative, right, star, textDecoration, top, underline, white, width, zIndex, (&), (?), (|*))
import CSS.Common (browsers)
import CSS.Cursor (Cursor(..), crosshair, default, pointer)
import CSS.Overflow (hidden, overflow, overflowY, scroll)

xtermCSS :: CSS
xtermCSS = do
  xterm ? do
    cursor Text
    position relative
    prefixed (browsers <> fromString "user-select") "none"
  xterm & byClass "focus" ? do
    key (fromString "outline") "none"
  xterm & pseudo "focus" ? do
    key (fromString "outline") "none"
  xterm |* helpers ? do
    position absolute
    top (px 0.0)
    zIndex 5
  xterm |* helpersTextarea ? do 
    padding (px 0.0) (px 0.0) (px 0.0) (px 0.0)
    key (fromString "border") 0.0
    margin (px 0.0) (px 0.0) (px 0.0) (px 0.0)
    position absolute
    opacity 0.0
    left (em (-9999.0))
    top (px 0.0)
    width (px 0.0)
    height (px 0.0)
    zIndex (-5)
    key (fromString "whitespace") "nowrap"
    overflow hidden
    key (fromString "resize") "none"
  xterm |* compositionView ? do
     backgroundColor black
     color white
     display displayNone
     position absolute
     key (fromString "white-space") "nowrap"
     zIndex 1
  xterm |* (compositionView & byClass "active") ? do
     display block
  xterm |* viewPort ? do
     backgroundColor black
     overflowY scroll
     cursor default
     position absolute
     right (px 0.0)
     left (px 0.0)
     top (px 0.0)
     bottom (px 0.0)
  xterm |* screen ? do
     position relative
  xterm |* (screen |* element "canvas") ? do
     position absolute
     left (px 0.0)
     top (px 0.0)
  xterm |* scrollArea ? do
     key (fromString "visibility") "hidden"
  charMeasureElement ? do
     display inlineBlock
     key (fromString "visibility") "hidden"
     position absolute
     top (px 0.0)
     left (em (-9999.0))
     key (fromString "line-height") "normal"
  xterm & byClass "enable-mouse-events" ? do
     cursor default
  xterm & byClass "xterm-cursor-pointer" ? do
     cursor pointer
  xterm |* (star & byClass "xterm-cursor-pointer") ? do
     cursor pointer
  (xterm & byClass "column-select") & byClass "focus" ? do
     cursor crosshair
  xterm |* accessibility ? accessibilityMessage
  xterm |* message ? accessibilityMessage
  xterm |* liveRegion ? do
     position absolute
     left (px (-9999.0))
     width (px 1.0)
     height (px 1.0)
     overflow hidden
  dim ? do
     key (fromString "opacity") "1 !important"
  underlines
  overlines
  star & byClass "xterm-strikethrough" ? do
     textDecoration lineThrough
  (screen |* decorationContainer) |* decoration ? do
     zIndex 6
     position absolute
  (screen |* decorationContainer) |* (decoration & byClass "xterm-decoration-top-layer") ? do
     zIndex 7
  overviewRuler ? do
     zIndex 8
     position absolute
     top (px 0.0)
     right (px 0.0)
     key (fromString "pointer-events") "none"
  decorationTop ? do
     zIndex 2
     position relative
  where
    xterm = star & byClass "xterm"
    helpers = star & byClass "xterm-helpers"
    helpersTextarea = star & byClass "xterm-helper-textarea"
    compositionView = star & byClass "composition-view"
    viewPort = star & byClass "xterm-viewport"
    screen = star & byClass "xterm-screen"
    scrollArea = star & byClass "xterm-scroll-area"
    charMeasureElement = star & byClass "xterm-char-measure-element"
    accessibility = star & byClass "xterm-accessibility"
    message = star & byClass "xterm-message"
    liveRegion = star & byClass "live-region"
    dim = star & byClass "xterm-dim"
    decorationContainer = star & byClass "xterm-decoration-container"
    decoration = star & byClass "xterm-decoration"
    overviewRuler = star & byClass "xterm-decoration-overview-ruler"
    decorationTop = star & byClass "xterm-decoration-top"
    accessibilityMessage = do
      position absolute
      left (px 0.0)
      top (px 0.0)
      bottom (px 0.0)
      right (px 0.0)
      zIndex 10
      key (fromString "color") "transparent"
      key (fromString "pointer-events") "none"
    underlines = do
      star & byClass "xterm-underline-1" ? do
         textDecoration underline
      star & byClass "xterm-underline-2" ? do
         key (fromString "text-decoration") "double underline"
      star & byClass "xterm-underline-3" ? do
         key (fromString "text-decoration") "wavy underline"
      star & byClass "xterm-underline-4" ? do
         key (fromString "text-decoration") "dotted underline"
      star & byClass "xterm-underline-5" ? do
         key (fromString "text-decoration") "dashed underline"
    overlines = do
      star & byClass "xterm-overline" ? do
         textDecoration overline

      (star & byClass "xterm-underline-1") &  byClass "xterm-overline" ? do
         key (fromString "text-decoration") "overline underline"
      (star & byClass "xterm-underline-2") &  byClass "xterm-overline" ? do
         key (fromString "text-decoration") "overline double underline"
      (star & byClass "xterm-underline-3") &  byClass "xterm-overline" ? do
         key (fromString "text-decoration") "overline wavy underline"
      (star & byClass "xterm-underline-4") &  byClass "xterm-overline" ? do
         key (fromString "text-decoration") "overline dotted underline"
      (star & byClass "xterm-underline-5") &  byClass "xterm-overline" ? do
         key (fromString "text-decoration") "overline dashed underline"

 
 
 
 
 
