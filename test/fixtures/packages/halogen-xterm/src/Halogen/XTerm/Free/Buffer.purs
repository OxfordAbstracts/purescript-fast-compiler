module Halogen.XTerm.Free.Buffer where

import Prelude

import Control.Monad.Free (Free, liftF, runFreeM)
import Control.Monad.Reader (ReaderT, ask)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Maybe (Maybe)
import Effect.Class (class MonadEffect, liftEffect)
import XTerm.Buffer (Buffer, BufferType)
import XTerm.Buffer as X
import XTerm.Buffer.Cell (BufferCell)
import XTerm.Buffer.Line (BufferLine)
import XTerm.Buffer.Line as L

runBuffer :: forall m a . MonadEffect m => MonadRec m => BufferM a -> ReaderT Buffer m a
runBuffer = runFreeM go
  where
    go (BufferType a) = do
      b <- ask
      liftEffect $ a <$> X.bufferType b
    go (CursorX a) = do
      b <- ask
      liftEffect $ a <$> X.cursorX b
    go (CursorY a) = do
      b <- ask
      liftEffect $ a <$> X.cursorY b
    go (ViewportY a) = do
      b <- ask
      liftEffect $ a <$> X.viewportY b
    go (BaseY a) = do
      b <- ask
      liftEffect $ a <$> X.baseY b
    go (BufferLength a) = do
      b <- ask
      liftEffect $ a <$> X.length b
    go (GetBufferLine i a) = do
      b <- ask
      liftEffect $ a <$> X.getLine b i
    go (IsWrapped l a) = do
      liftEffect $ a <$> L.isWrapped l
    go (LineLength l a) = do
      liftEffect $ a <$> L.length l
    go (GetNullCell a) = do
      b <- ask
      liftEffect $ a <$> X.getNullCell b


data BufferF a =
    BufferType (BufferType -> a)
  | CursorX (Int -> a)
  | CursorY (Int -> a)
  | ViewportY (Int -> a)
  | BaseY (Int -> a)
  | BufferLength (Int -> a)
  | GetBufferLine Int (Maybe BufferLine -> a)
  | IsWrapped BufferLine (Boolean -> a)
  | LineLength BufferLine (Int -> a)
  | GetNullCell (BufferCell -> a)


instance Functor BufferF where
  map f (BufferType e) = BufferType (f <<< e)
  map f (CursorX e) = CursorX (f <<< e)
  map f (CursorY e) = CursorY (f <<< e)
  map f (ViewportY e) = ViewportY (f <<< e)
  map f (BaseY e) = BaseY (f <<< e)
  map f (BufferLength e) = BufferLength (f <<< e)
  map f (GetBufferLine l e) = GetBufferLine l (f <<< e)
  map f (IsWrapped l e) = IsWrapped l (f <<< e)
  map f (LineLength l e) = LineLength l (f <<< e)
  map f (GetNullCell e) = GetNullCell (f <<< e)


type BufferM = Free BufferF 

bufferType :: BufferM BufferType
bufferType = liftF $ BufferType identity

cursorX :: BufferM Int
cursorX = liftF $ CursorX identity

cursorY :: BufferM Int
cursorY = liftF $ CursorY identity

viewportY :: BufferM Int
viewportY = liftF $ ViewportY identity

baseY :: BufferM Int
baseY = liftF $ BaseY identity

bufferLength :: BufferM Int 
bufferLength = liftF $ BufferLength identity

getBufferLine :: Int -> BufferM (Maybe BufferLine)
getBufferLine l = liftF $ GetBufferLine l identity

getNullCell :: BufferM BufferCell
getNullCell = liftF $ GetNullCell identity

isWrapped :: BufferLine -> BufferM Boolean
isWrapped l = liftF $ IsWrapped l identity

lineLength :: BufferLine -> BufferM Int
lineLength l = liftF $ LineLength l identity

