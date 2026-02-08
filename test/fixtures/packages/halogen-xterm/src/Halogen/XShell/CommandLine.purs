-- | A collection of command line interface building utilities. [See example implementation](https://github.com/grybiena/grybiena.github.io/blob/2388184bcf26dfa3bfa8d5209e53f40c313df0e0/halogen-xterm-example/src/Example.purs) for a usage example.
module Halogen.XShell.CommandLine where

import Prelude

import Control.Monad.Rec.Class (class MonadRec)
import Data.Array (filter, head, tail)
import Data.Lens (Lens', _1, _2, lens', (%~), (.~), (^.))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.String (Pattern(..), joinWith, length, null, split, trim)
import Data.String.CodeUnits (dropRight, takeRight)
import Data.Traversable (traverse, traverse_)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Console (log)
import Halogen.XShell (interpreter)
import Halogen.XShell.Free (ShellM, getShell, modifyShell, terminal)
import Halogen.XTerm as Terminal
import Halogen.XTerm.Free (options, withActiveBuffer, write, writeLn)
import Halogen.XTerm.Free.Buffer (bufferLength, cursorX, getBufferLine, lineLength)
import Halogen.XTerm.Free.Options (setCursorBlink)

class CommandLine shell where
  cmd :: Lens' shell String
  prompt :: Lens' shell String

instance CommandLine (String /\ String) where
  cmd = _2
  prompt = _1

newtype ShellState w o m =
  ShellState {
    prompt :: String
  , command :: String
  , commandEnv :: Array (Command w o m)
  , foreground :: Maybe (ProcessHandle w o m)
  }

instance CommandLine (ShellState w o m) where
  cmd = lens' (\(ShellState s) -> s.command /\ (\c -> ShellState (s { command = c }))) 
  prompt = lens' (\(ShellState s) -> s.prompt /\ (\c -> ShellState (s { prompt = c }))) 

type ProcessHandle w o m =
  { stdin :: String -> ShellM w (ShellState w o m) o m Unit
  , kill :: ShellM w (ShellState w o m) o m Unit
  }

type Command w o m =
  { name :: String
  , description :: Array String
  , cmd :: Array String -> ShellM w (ShellState w o m) o m Unit
  }

commandLine :: forall w s o m .
            MonadEffect m
         => CommandLine s
         => ShellM w s o m Unit 
         -> String -> ShellM w s o m Unit 
commandLine runCommand =
  case _ of
    -- Ctrl+C
    "\x0003" -> do
       modifyShell (cmd .~ "")
       shell <- getShell
       terminal do
         write "^C"
         write ("\r\n" <> (shell ^. prompt))
    -- Enter
    "\r" -> do
       runCommand
    -- BackSpace
    "\x007F" -> backspace
    -- Printable characters
    e | e >= "\x20" && e <= "\x7E" || e >= "\x00a0" -> do
      modifyShell (cmd %~ (_ <> e))
      terminal $ write e
    e -> do
      liftEffect $ log $ "non-printable: " <> e
      pure unit
 
backspace :: forall w s o m .
            MonadEffect m
         => CommandLine s
         => ShellM w s o m Unit 
backspace = do
  shell <- getShell
  terminal do
    x <- withActiveBuffer cursorX
    if (x == 0)
      then do
        write "\x1bM"
        ll <- withActiveBuffer do
           blen <- bufferLength
           blin <- getBufferLine (blen-1) 
           traverse lineLength blin
        write "\x9bK"
        flip traverse_ ll $ \l ->
          if (length (shell ^. cmd) - 1 <= l)
            then do
               write (shell ^. prompt)
               write (dropRight 1 (shell ^. cmd))
            else do
               write (dropRight 1 $ takeRight l (shell ^. cmd))
       else
         when (length (shell ^. cmd) > 0) do
           write "\x08 \x08"
  modifyShell (cmd %~ dropRight 1)


textInterpreter :: forall w s o m .
            MonadEffect m
         => (String -> ShellM w s o m Unit)
         -> Terminal.Output -> ShellM w s o m Unit 
textInterpreter interpret =
  case _ of
    Terminal.Data d -> interpret d
    Terminal.LineFeed -> liftEffect $ log "line feed"
    _ -> pure unit

runRepl :: forall w s o m .
        MonadEffect m
     => CommandLine s
     => (String -> ShellM w s o m String)
     -> ShellM w s o m Unit 
runRepl repl = do 
  shell <- getShell
  modifyShell (cmd .~ "")
  res <- repl (shell ^. cmd)
  terminal do
    when (not $ null $ trim (shell ^. cmd)) $
      write ("\r\n" <> res) 
    write ("\r\n" <> (shell ^. prompt))

canceler :: forall w o m . MonadAff m => MonadRec m => Terminal.Output -> ShellM w (ShellState w o m) o m Unit
canceler = textInterpreter $ case _ of 
                                -- Ctrl+C
                                "\x0003" -> do
                                   terminal $ write "^C"
                                   cancel
                                s -> commandLine attach s

cancel :: forall w o m . MonadAff m => MonadRec m => ShellM w (ShellState w o m) o m Unit
cancel = do 
  ShellState sh <- getShell
  flip traverse_ sh.foreground $ \f -> do
     f.kill
  modifyShell (\(ShellState st) -> ShellState (st { foreground = Nothing }))
  modifyShell (cmd .~ "")
  shell' <- getShell
  terminal do
    options $ setCursorBlink true
    write ("\r\n" <> (shell' ^. prompt))
  interpreter (textInterpreter $ commandLine (prog sh.commandEnv))


attach :: forall w o m . MonadAff m => ShellM w (ShellState w o m) o m Unit
attach = do
  sh@(ShellState { foreground }) <- getShell
  flip traverse_ foreground $ \f -> do
    f.stdin (sh ^. cmd)
  terminal $ write "\r\n"
  modifyShell (cmd .~ "")


commandMap :: forall w o m.
              MonadAff m
           => MonadRec m
           => Array (Command w o m) -> Map String (Array String -> ShellM w (ShellState w o m) o m Unit)
commandMap cmds = Map.insert "help" helpCmd (Map.fromFoldable ((\cmd -> cmd.name /\ cmd.cmd) <$> cmds))
  where
    helpCmd _ = do
       terminal $ writeLn $ helpText cmds
       shell' <- getShell
       terminal $ write (shell' ^. prompt)
       modifyShell (cmd .~ "")

    helpText a = helpTxt <> joinWith "" (cmdHelp <$> a) 
      where
        helpTxt = "\r\n  " <> "help" <> "\r\n    show this help text"
        cmdHelp cmd = "\r\n  " <> cmd.name <> "\r\n    " <> (joinWith "\r\n    " cmd.description)


prog :: forall w o m . MonadAff m => MonadRec m => Array (Command w o m) -> ShellM w (ShellState w o m) o m Unit
prog commands = do
  let cmds = commandMap commands
  sh <- getShell
  let cmdArgs = filter (not <<< null) $ split (Pattern " ") (sh ^. cmd)
  case head cmdArgs of    
    Nothing -> do 
      terminal do
        writeLn $ ""
      shell' <- getShell
      terminal $ write (shell' ^. prompt)
      modifyShell (cmd .~ "")
    Just c ->
      case Map.lookup c cmds of
        Just run -> run $ maybe [] identity (tail cmdArgs)
        Nothing -> do
          terminal do
            writeLn $ "\r\nunrecognised command \"" <> c <> "\" - type \"help\" to see the available commands"
          shell' <- getShell
          terminal $ write (shell' ^. prompt)
          modifyShell (cmd .~ "")


