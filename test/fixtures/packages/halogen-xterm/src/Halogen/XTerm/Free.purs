module Halogen.XTerm.Free where

import Prelude

import Control.Monad.Free (Free, liftF, runFreeM)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Either (hush, isRight)
import Data.Maybe (Maybe(..))
import Effect.Aff (launchAff_, try)
import Effect.Aff.AVar as AVar
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect)
import Halogen.XTerm.Free.Buffer (BufferM, runBuffer)
import Halogen.XTerm.Free.Options (OptionsM, runOptions)
import Web.DOM (Element)
import XTerm.Addons (class Addon, FitAddon, TerminalAddon, WebGLAddon, WebLinksAddon, addon)
import XTerm.Addons as XA
import XTerm.Buffer.Namespace as XB
import XTerm.Marker (Marker)
import XTerm.Terminal (Terminal, getOptions)
import XTerm.Terminal as XT


runTerminal :: forall m a .
               MonadAff m
            => MonadRec m
            => TerminalM a
            -> ReaderT Terminal m a
runTerminal = runFreeM go
  where
    go (Options o) = do
       terminal <- ask
       runReaderT (runOptions o) (getOptions terminal)
    go (TerminalElement a) = do
      terminal <- ask
      liftEffect $ a <$> XT.element terminal
    go (TextArea a) = do
      terminal <- ask
      liftEffect $ a <$> XT.textarea terminal
    go (Rows a) = do
      terminal <- ask
      liftEffect $ a <$> XT.rows terminal
    go (Cols a) = do
      terminal <- ask
      liftEffect $ a <$> XT.cols terminal
    go (WithActiveBuffer f) = do
      terminal <- ask
      liftEffect $ runReaderT (runBuffer f) (XB.active $ XT.buffer terminal)
    go (WithNormalBuffer f) = do
      terminal <- ask
      liftEffect $ runReaderT (runBuffer f) (XB.normal $ XT.buffer terminal)
    go (WithAlternateBuffer f) = do
      terminal <- ask
      liftEffect $ runReaderT (runBuffer f) (XB.alternate $ XT.buffer terminal)
    go (Markers f) = do
      terminal <- ask
      liftEffect $ f <$> XT.markers terminal
    go (Write s a) = do
      terminal <- ask
      sem <- liftAff $ AVar.empty
      liftEffect $ XT.write terminal s (launchAff_ $ AVar.put a sem)
      liftAff $ AVar.take sem
    go (WriteLn s a) = do
      terminal <- ask
      sem <- liftAff $ AVar.empty
      liftEffect $ XT.writeln terminal s (launchAff_ $ AVar.put a sem)
      liftAff $ AVar.take sem
    go (FitAddon a) = do
      liftEffect $ (a <<< hush) <$> try XA.fitAddon
    go (WebLinksAddon a) = do
      liftEffect $ (a <<< hush) <$> try XA.webLinksAddon 
    go (WebGLAddon a) = do
      liftEffect $ (a <<< hush) <$> try XA.webGLAddon 
    go (LoadAddon t a) = do
       terminal <- ask
       liftEffect $ (a <<< isRight) <$> try (XT.loadAddon terminal t)

data TerminalF a =
    Options (OptionsM a)
  | TerminalElement (Maybe Element -> a)
  | TextArea (Maybe Element -> a)
  | Rows (Int -> a)
  | Cols (Int -> a)
  | WithActiveBuffer (BufferM a) 
  | WithNormalBuffer (BufferM a)
  | WithAlternateBuffer (BufferM a)
  | Markers (Array Marker -> a)
  | Write String a
  | WriteLn String a
  | FitAddon (Maybe FitAddon -> a)
  | WebLinksAddon (Maybe WebLinksAddon -> a)
  | WebGLAddon (Maybe WebGLAddon -> a)
  | LoadAddon TerminalAddon (Boolean -> a)

instance Functor TerminalF where
  map f (Options o) = Options (f <$> o)
  map f (TerminalElement e) = TerminalElement (f <<< e)
  map f (TextArea e) = TextArea (f <<< e)
  map f (Rows e) = Rows (f <<< e)
  map f (Cols e) = Cols (f <<< e)
  map f (WithActiveBuffer b) = WithActiveBuffer (f <$> b)
  map f (WithNormalBuffer b) = WithNormalBuffer (f <$> b)
  map f (WithAlternateBuffer b) = WithAlternateBuffer (f <$> b)
  map f (Markers m) = Markers (f <<< m)
  map f (Write s a) = Write s (f a)
  map f (WriteLn s a) = WriteLn s (f a)
  map f (FitAddon a) = FitAddon (f <<< a)
  map f (WebLinksAddon a) = WebLinksAddon (f <<< a)
  map f (WebGLAddon a) = WebGLAddon (f <<< a)
  map f (LoadAddon t a) = LoadAddon t (f <<< a)

type TerminalM = Free TerminalF 

options :: forall a . OptionsM a -> TerminalM a
options = liftF <<< Options

terminalElement :: TerminalM (Maybe Element)
terminalElement = liftF $ TerminalElement identity

textArea :: TerminalM (Maybe Element)
textArea = liftF $ TextArea identity

rows :: TerminalM Int
rows = liftF $ Rows identity

cols :: TerminalM Int
cols = liftF $ Cols identity

withActiveBuffer :: forall a . BufferM a -> TerminalM a
withActiveBuffer b = liftF $ WithActiveBuffer b

withNormalBuffer :: forall a . BufferM a -> TerminalM a
withNormalBuffer b = liftF $ WithNormalBuffer b

withAlternateBuffer :: forall a . BufferM a -> TerminalM a
withAlternateBuffer b = liftF $ WithAlternateBuffer b

markers :: TerminalM (Array Marker)
markers = liftF $ Markers identity

write :: String -> TerminalM Unit
write s = liftF $ Write s unit

writeLn :: String -> TerminalM Unit
writeLn s = liftF $ WriteLn s unit

fitAddon :: TerminalM (Maybe FitAddon)
fitAddon = liftF $ FitAddon identity

webLinksAddon :: TerminalM (Maybe WebLinksAddon)
webLinksAddon = liftF $ WebLinksAddon identity

webGLAddon :: TerminalM (Maybe WebGLAddon)
webGLAddon = liftF $ WebGLAddon identity

loadAddon :: forall a . Addon a => a -> TerminalM Boolean
loadAddon t = liftF $ LoadAddon (addon t) identity


loadAddons :: Boolean -> TerminalM Unit
loadAddons verbose = do
  wgl <- webGLAddon
  case wgl of
    Nothing -> when verbose $ writeLn "WebGL Addon unavailable"
    Just addon -> do
      when verbose $ write "Loading WebGL "
      ok <- loadAddon addon
      when verbose $ if ok then writeLn "OK" else writeLn "FAILED"
  wli <- webLinksAddon
  case wli of
    Nothing -> when verbose $ writeLn "WebLinks Addon unavailable"
    Just addon -> do
      when verbose $ write "Loading WebLinks "
      ok <- loadAddon addon
      when verbose $ if ok then writeLn "OK" else writeLn "FAILED"


