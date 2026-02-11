module Props.Setters where

import Prelude

padding
  :: forall f r
   . Applicative f
  => Number
  -> Record (padding :: f Number | r)
  -> Record (padding :: f Number | r)
padding i old = old { padding = pure i }

flexDirection
  :: forall f r
   . Applicative f
  => String
  -> Record (flexDirection :: f String | r)
  -> Record (flexDirection :: f String | r)
flexDirection i old = old { flexDirection = pure i }

marginTop
  :: forall f r
   . Applicative f
  => Int
  -> Record (marginTop :: f Int | r)
  -> Record (marginTop :: f Int | r)
marginTop i old = old { marginTop = pure i }

marginBottom
  :: forall f r
   . Applicative f
  => Int
  -> Record (marginBottom :: f Int | r)
  -> Record (marginBottom :: f Int | r)
marginBottom i old = old { marginBottom = pure i }

backgroundColor
  :: forall f r
   . Applicative f
  => String
  -> Record (backgroundColor :: f String | r)
  -> Record (backgroundColor :: f String | r)
backgroundColor i old = old { backgroundColor = pure i }

width
  :: forall f r
   . Applicative f
  => String
  -> Record (width :: f String | r)
  -> Record (width :: f String | r)
width i old = old { width = pure i }

justifyContent
  :: forall f r
   . Applicative f
  => String
  -> Record (justifyContent :: f String | r)
  -> Record (justifyContent :: f String | r)
justifyContent i old = old { justifyContent = pure i }

height
  :: forall f r
   . Applicative f
  => String
  -> Record (height :: f String | r)
  -> Record (height :: f String | r)
height i old = old { height = pure i }

color
  :: forall f r
   . Applicative f
  => String
  -> Record (color :: f String | r)
  -> Record (color :: f String | r)
color i old = old { color = pure i }

dimColor
  :: forall f r
   . Applicative f
  => Boolean
  -> Record (dimColor :: f Boolean | r)
  -> Record (dimColor :: f Boolean | r)
dimColor i old = old { dimColor = pure i }

bold
  :: forall f r
   . Applicative f
  => Boolean
  -> Record (bold :: f Boolean | r)
  -> Record (bold :: f Boolean | r)
bold i old = old { bold = pure i }

italic
  :: forall f r
   . Applicative f
  => Boolean
  -> Record (italic :: f Boolean | r)
  -> Record (italic :: f Boolean | r)
italic i old = old { italic = pure i }

underline
  :: forall f r
   . Applicative f
  => Boolean
  -> Record (underline :: f Boolean | r)
  -> Record (underline :: f Boolean | r)
underline i old = old { underline = pure i }

strikethrough
  :: forall f r
   . Applicative f
  => Boolean
  -> Record (strikethrough :: f Boolean | r)
  -> Record (strikethrough :: f Boolean | r)
strikethrough i old = old { strikethrough = pure i }

inverse
  :: forall f r
   . Applicative f
  => Boolean
  -> Record (inverse :: f Boolean | r)
  -> Record (inverse :: f Boolean | r)
inverse i old = old { inverse = pure i }

wrap
  :: forall f r
   . Applicative f
  => Boolean
  -> Record (wrap :: f Boolean | r)
  -> Record (wrap :: f Boolean | r)
wrap i old = old { wrap = pure i }
