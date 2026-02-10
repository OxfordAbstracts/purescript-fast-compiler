module Halogen.XShell
  ( component
  , module Shell
  ) where

import Prelude

import Control.Monad.Free (runFreeM)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Data.Maybe (Maybe(..))
import Data.Options ((:=))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.Data.Slot as Slot
import Halogen.HTML as HH
import Halogen.XShell.Free (Action(..), ShellF(..), ShellM(..), XShell, Slots, renderWindows)
import Halogen.XShell.Free (
   terminal
 , getShell
 , putShell
 , modifyShell
 , interpreter
 , output
 , openWindow
 , queryWindow
 , closeWindow
 ) as Shell
import Halogen.XTerm as Terminal
import Type.Proxy (Proxy(..))
import XTerm.Options (cursorBlink, fontFamily)
import XTerm.Terminal (new)

_terminal = Proxy :: Proxy "terminal"

component :: forall w s o m. MonadAff m => H.Component (ShellM w s o m) s o m
component = do
  H.mkComponent
    { initialState: \shell -> { shell, interpreter: const (pure unit), terminal: Nothing, windows: Slot.empty }
    , render
    , eval: H.mkEval $ H.defaultEval { handleAction = handleAction
                                     , handleQuery = runShellM 
                                     , initialize = Just Initialize
                                     }
    }

render :: forall w s o m. MonadAff m => XShell w s o m -> H.ComponentHTML (Action w s o m) (Slots w) m
render { terminal, windows } =
  HH.div_
    ([ case terminal of
         Nothing -> HH.div_ []
         Just te -> HH.slot _terminal unit Terminal.component te TerminalOutput
     ]
     <> renderWindows windows

   )

handleAction :: forall w s o m .
                MonadAff m
             => Action w s o m
             -> H.HalogenM (XShell w s o m) (Action w s o m) (Slots w) o m Unit
handleAction = case _ of
  Initialize -> do
    terminal <- H.liftEffect $ new (fontFamily := "\"Cascadia Code\", Menlo, monospace"
                                 <> cursorBlink := true
                                   ) mempty
    H.modify_ (\st -> st { terminal = Just terminal })
  TerminalOutput output -> do
     { interpreter } <- H.get
     void $ runShellM $ interpreter output
  RunShell f -> void $ runShellM f 



runShellM :: forall w s o m a .
            MonadAff m
         => ShellM w s o m a
         -> H.HalogenM (XShell w s o m) (Action w s o m) (Slots w) o m (Maybe a)
runShellM (ShellM s) = runMaybeT $ runFreeM go s
  where
    go (Terminal f) = do
      r <- H.lift $ H.query _terminal unit f
      MaybeT $ pure r
    go (Lift m) = MaybeT $ Just <$> H.lift m
    go (GetShell a) = do
      { shell } <- H.lift H.get
      pure $ a shell
    go (PutShell sh a) = do
      H.modify_ (\st -> st { shell = sh })
      pure a
    go (Interpreter i a) = do
      H.modify_ (\st -> st { interpreter = i })
      pure a
    go (Output o a) = do
      H.lift $ H.raise o
      pure a
    go (LiftHalogen f) = MaybeT $ Just <$> f
    go (GetWindowSlots f) = do
      { windows } <- H.get
      pure $ f windows 
    go (ModifyWindowSlots f a) = do
      H.modify_ (\st -> st { windows = f st.windows })
      pure a

