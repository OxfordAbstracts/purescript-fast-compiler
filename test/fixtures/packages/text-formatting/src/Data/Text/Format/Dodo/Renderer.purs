module Data.Text.Format.Dodo.Renderer where

import Prelude

import Type.Proxy (Proxy)

import Data.Text.Output (OutputKind)
import Data.Text.Format.Dodo.Format
    ( Directive(..) ) as X
import Data.Text.Format.Dodo.WrapRule as WR


class Renderer (x :: OutputKind) where
    render :: forall a. Proxy x -> X.Directive -> WR.WrapRule a