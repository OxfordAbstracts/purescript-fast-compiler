module XTerm.LinkProvider where

import Control.Alt (class Functor, (<$>))
import Data.Unit (Unit)
import Effect (Effect)
import XTerm.Link (ILink, Link, makeLink)


newtype BufferLineNumber = BufferLineNumber Int

type ILinkCallback = Array ILink -> Effect Unit
type ILinkProvider = BufferLineNumber -> ILinkCallback -> Effect Unit

type LinkCallback = Array Link -> Effect Unit
type LinkProvider = BufferLineNumber -> LinkCallback -> Effect Unit

makeLinkProvider :: LinkProvider -> ILinkProvider
makeLinkProvider p = \b c -> p b (over makeLink c)
  where
   over :: forall f a b c . Functor f => (a -> b) -> (f b -> c) -> (f a -> c)
   over f g = \x -> g (f <$> x)

