module Halogen.XTerm
  ( Output(..)
  , component
  , module XTermCSS
  , module XTermFree
  , module XTermFreeOptions
  , module XTermFreeBuffer
  ) where

import Prelude

import Control.Monad.Reader (runReaderT)
import Data.Array ((:))
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse_)
import Effect.Aff.Class (class MonadAff)
import Effect.Console (log)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.CSS (stylesheet)
import Halogen.HTML.Properties as HP
import Halogen.Subscription as HS
import Halogen.XTerm.CSS (xtermCSS)
import Halogen.XTerm.CSS (xtermCSS) as XTermCSS
import Halogen.XTerm.Free (
    TerminalM
  , options
  , terminalElement
  , textArea
  , rows
  , cols
  , withActiveBuffer
  , withNormalBuffer
  , withAlternateBuffer
  , markers
  , write
  , writeLn
  , fitAddon
  , webLinksAddon
  , webGLAddon
  , loadAddon
  , loadAddons
  ) as XTermFree
import Halogen.XTerm.Free (TerminalM, runTerminal)
import Halogen.XTerm.Free.Options (
    OptionsM
  , getCursorBlink
  , setCursorBlink
  , getFontFamily
  , setFontFamily
  ) as XTermFreeOptions
import Halogen.XTerm.Free.Buffer (
    BufferM
  , bufferType
  , cursorX
  , cursorY
  , viewportY
  , baseY
  , bufferLength
  , getBufferLine
  , getNullCell
  , isWrapped
  , lineLength
  ) as XTermFreeBuffer
import XTerm.Disposable (Disposable, dispose)
import XTerm.Terminal (BinaryString, Key, RowRange, Terminal, ViewportSize, ViewportYOffset, onBell, onBinary, onData, onKey, onLineFeed, onRender, onResize, onScroll, onSelectionChange, onTitleChange, onWriteParsed, openTerminal)

type State =
  { terminal :: Terminal
  , disposables :: Array Disposable
  }

data Action = 
    Initialize
  | Finalize
  | Raise Output

data Output =
    Data String
  | Binary BinaryString
  | Bell
  | Key Key
  | LineFeed
  | Render RowRange
  | WriteParsed
  | Resize ViewportSize
  | Scroll ViewportYOffset
  | SelectionChange
  | TitleChange String

component :: forall m. MonadAff m => H.Component TerminalM Terminal Output m
component = do
  H.mkComponent
    { initialState: \terminal -> { terminal, disposables: [] }
    , render
    , eval: H.mkEval $ H.defaultEval { handleAction = handleAction
                                     , handleQuery = handleQuery 
                                     , initialize = Just Initialize
                                     , finalize = Just Finalize
                                     }
    }


render :: forall m. MonadAff m => State -> H.ComponentHTML Action () m
render _ = HH.div_
             [ stylesheet xtermCSS
             , HH.div [ HP.ref (H.RefLabel "terminal")] []
             ] 

handleAction :: forall m .
                MonadAff m
             => Action
             -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    e <- H.getRef (H.RefLabel "terminal")
    case e of
      Nothing -> H.liftEffect $ log "no terminal element"
      Just el -> do
        { terminal } <- H.get
        H.liftEffect $ openTerminal terminal el
        outputBell terminal
        outputBinary terminal
        outputKey terminal
        outputLineFeed terminal
        outputRender terminal
        outputWriteParsed terminal
        outputResize terminal
        outputScroll terminal
        outputSelectionChange terminal
        outputTitleChange terminal
        outputData terminal
  Finalize -> do
    { disposables } <- H.get
    H.liftEffect $ traverse_ dispose disposables
  Raise o -> H.raise o
  where
    outputBell terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onBell terminal (HS.notify listener $ Raise $ Bell) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputBinary terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onBinary terminal (HS.notify listener <<< Raise <<< Binary) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputKey terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onKey terminal (HS.notify listener <<< Raise <<< Key) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputLineFeed terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onLineFeed terminal (HS.notify listener $ Raise $ LineFeed) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputRender terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onRender terminal (HS.notify listener <<< Raise <<< Render) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputWriteParsed terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onWriteParsed terminal (HS.notify listener $ Raise $ WriteParsed) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputResize terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onResize terminal (HS.notify listener <<< Raise <<< Resize) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputScroll terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onScroll terminal (HS.notify listener <<< Raise <<< Scroll) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputSelectionChange terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onSelectionChange terminal (HS.notify listener $ Raise $ SelectionChange) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputTitleChange terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onTitleChange terminal (HS.notify listener <<< Raise <<< TitleChange) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })
    outputData terminal = do
      { listener, emitter } <- H.liftEffect HS.create
      disposable <- H.liftEffect $ onData terminal (HS.notify listener <<< Raise <<< Data) 
      _ <- H.subscribe emitter 
      H.modify_ (\st -> st { disposables = disposable:st.disposables })



handleQuery :: forall m a .
                MonadAff m
             => TerminalM a
             -> H.HalogenM State Action () Output m (Maybe a)
handleQuery f = do 
  { terminal } <- H.get
  H.liftAff $ Just <$> runReaderT (runTerminal f) terminal


