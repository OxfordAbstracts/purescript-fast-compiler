module Halogen.XShell.Free where

import Prelude

import Control.Monad.Cont (class MonadTrans, lift)
import Control.Monad.Free (Free, liftF)
import Control.Monad.Rec.Class (class MonadRec)
import Control.Monad.State (State, execState)
import Data.Array (cons)
import Data.Maybe (Maybe, maybe)
import Data.Symbol (class IsSymbol)
import Data.Tuple (snd)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen as H
import Halogen.Data.Slot (Slot, SlotStorage, foreachSlot)
import Halogen.Data.Slot as Slots
import Halogen.HTML as HH
import Halogen.XTerm as Terminal
import Halogen.XTerm.Free (TerminalM)
import Prim.Row (class Cons)
import Type.Prelude (Proxy)
import XTerm.Terminal (Terminal)

type Slots w =
  ( terminal :: H.Slot TerminalM Terminal.Output Unit
  | w
  )

type XShell w s o m =
  { shell :: s 
  , interpreter :: Terminal.Output -> ShellM w s o m Unit
  , terminal :: Maybe Terminal
  , windows :: WindowSlots w s o m 
  }


newtype WindowSlot w s o m query output = 
  WindowSlot {
    window :: H.ComponentHTML (Action w s o m) (Slots w) m
  }

data Action w s o m =
    Initialize
  | TerminalOutput Terminal.Output
  | RunShell (ShellM w s o m Unit)


renderWindows :: forall w s o m. WindowSlots w s o m -> Array (H.ComponentHTML (Action w s o m) (Slots w) m)
renderWindows slots = execState (foreachSlot slots renderWindows') []
  where
    renderWindows' :: forall query output.
                      WindowSlot w s o m query output -> State (Array (H.ComponentHTML (Action w s o m) (Slots w) m)) Unit 
    renderWindows' (WindowSlot { window }) = H.modify_ (cons window)

type WindowSlots w s o m = SlotStorage w (WindowSlot w s o m)


data ShellF w s o m r =
    Terminal (TerminalM r)
  | Lift (m r)
  | GetShell (s -> r)
  | PutShell s r
  | Interpreter (Terminal.Output -> ShellM w s o m Unit) r
  | Output o r
  | LiftHalogen (H.HalogenM (XShell w s o m) (Action w s o m) (Slots w) o m r) 
  | GetWindowSlots (WindowSlots w s o m -> r)
  | ModifyWindowSlots (WindowSlots w s o m -> WindowSlots w s o m) r


instance Functor m => Functor (ShellF w s o m) where
  map f (Terminal t) = Terminal (f <$> t)
  map f (Lift q) = Lift (f <$> q)
  map f (GetShell s) = GetShell (f <<< s)
  map f (PutShell s a) = PutShell s (f a)
  map f (Interpreter s a) = Interpreter s (f a)
  map f (Output o a) = Output o (f a)
  map f (LiftHalogen m) = LiftHalogen (f <$> m)
  map f (GetWindowSlots s) = GetWindowSlots (f <<< s)
  map f (ModifyWindowSlots s a) = ModifyWindowSlots s (f a)


type Shell w s o m = Free (ShellF w s o m)

newtype ShellM w s o m r = ShellM (Shell w s o m r)

instance MonadTrans (ShellM w s o) where
  lift = ShellM <<< liftF <<< Lift

instance MonadEffect m => MonadEffect (ShellM w s o m) where
  liftEffect = lift <<< liftEffect

instance MonadAff m => MonadAff (ShellM w s o m) where
  liftAff = lift <<< liftAff

derive newtype instance MonadRec (ShellM w s o m)
derive newtype instance Functor (ShellM w s o m)
derive newtype instance Apply (ShellM w s o m)
derive newtype instance Applicative (ShellM w s o m)
derive newtype instance Bind (ShellM w s o m)
derive newtype instance Monad (ShellM w s o m)

terminal :: forall w s o m r . TerminalM r -> ShellM w s o m r
terminal = ShellM <<< liftF <<< Terminal

getShell :: forall w s o m . ShellM w s o m s
getShell = ShellM $ liftF $ GetShell identity 

putShell :: forall w s o m . s -> ShellM w s o m Unit
putShell s = ShellM $ liftF $ PutShell s unit

modifyShell :: forall w s o m . (s -> s) -> ShellM w s o m Unit
modifyShell f = do
  cmd <- getShell
  putShell (f cmd)

interpreter :: forall w s o m . (Terminal.Output -> ShellM w s o m Unit) -> ShellM w s o m Unit
interpreter i = ShellM $ liftF $ Interpreter i unit

output :: forall w s o m . o -> ShellM w s o m Unit
output o = ShellM $ liftF $ Output o unit

liftHalogen :: forall w s o m r . H.HalogenM (XShell w s o m) (Action w s o m) (Slots w) o m r -> ShellM w s o m r
liftHalogen f = ShellM $ liftF $ LiftHalogen f 


modifyWindowSlots :: forall w s o m . (WindowSlots w s o m -> WindowSlots w s o m) -> ShellM w s o m Unit
modifyWindowSlots f = ShellM $ liftF $ ModifyWindowSlots f unit

openWindow :: forall q' o' i' _1 s o sym px i w m.
             Cons sym (Slot q' o' i) _1 (Slots w)
          => IsSymbol sym
          => Ord i
          => Cons sym (Slot q' o' i) px w
          => Proxy sym
          -> i
          -> H.Component q' i' o' m
          -> i' -> (o' -> ShellM w s o m Unit) -> ShellM w s o m Unit
openWindow label i component input actout = do
  let window = HH.slot label i component input (RunShell <<< actout) 
  modifyWindowSlots (Slots.insert label i (WindowSlot { window }))

queryWindow :: forall q o' _1 s o sym px i w m a.
             Cons sym (Slot q o' i) _1 (Slots w)
          => IsSymbol sym
          => Ord i
          => Cons sym (Slot q o' i) px w
          => Proxy sym
          -> i
          -> q a 
          -> ShellM w s o m (Maybe a)
queryWindow label i query = liftHalogen (H.query label i query)

closeWindow :: forall q' o' _1 s o sym px i w m.
             Cons sym (Slot q' o' i) _1 (Slots w)
          => IsSymbol sym
          => Ord i
          => Cons sym (Slot q' o' i) px w
          => Proxy sym
          -> i
          -> ShellM w s o m Unit
closeWindow label i = do
  modifyWindowSlots (\ss -> maybe ss snd (Slots.pop label i ss))


