module Halogen.XTerm.Free.Options where

import Prelude

import Control.Monad.Free (Free, liftF, runFreeM)
import Control.Monad.Reader (ReaderT, ask)
import Control.Monad.Rec.Class (class MonadRec)
import Effect.Class (class MonadEffect, liftEffect)
import XTerm.Options (TerminalOptions)
import XTerm.Options as XO

runOptions :: forall m a .
               MonadEffect m
            => MonadRec m
            => OptionsM a
            -> ReaderT TerminalOptions m a
runOptions = runFreeM go
  where
    go (GetCursorBlink f) = do
       opts <- ask
       liftEffect $ f <$> XO.getCursorBlink opts
    go (SetCursorBlink b a) = do
       opts <- ask
       liftEffect $ XO.setCursorBlink opts b
       pure a
    go (GetFontFamily f) = do
       opts <- ask
       liftEffect $ f <$> XO.getFontFamily opts
    go (SetFontFamily b a) = do
       opts <- ask
       liftEffect $ XO.setFontFamily opts b
       pure a


data OptionsF a =
    GetCursorBlink (Boolean -> a)
  | SetCursorBlink Boolean a
  | GetFontFamily (String -> a)
  | SetFontFamily String a

type OptionsM = Free OptionsF

instance Functor OptionsF where
  map f (GetCursorBlink g) = GetCursorBlink (f <<< g)
  map f (SetCursorBlink b a) = SetCursorBlink b (f a)
  map f (GetFontFamily g) = GetFontFamily (f <<< g)
  map f (SetFontFamily b a) = SetFontFamily b (f a)


getCursorBlink :: OptionsM Boolean
getCursorBlink = liftF $ GetCursorBlink identity

setCursorBlink :: Boolean -> OptionsM Unit
setCursorBlink b = liftF $ SetCursorBlink b unit

getFontFamily :: OptionsM String
getFontFamily = liftF $ GetFontFamily identity

setFontFamily :: String -> OptionsM Unit
setFontFamily b = liftF $ SetFontFamily b unit


