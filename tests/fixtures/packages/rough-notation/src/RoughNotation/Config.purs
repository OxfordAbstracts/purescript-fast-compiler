module RoughNotation.Config
  ( BracketType(..)
  , Config
  , ConfigRows
  , NativeConfig
  , RoughAnnotationType(..)
  , RoughPadding(..)
  , defaultConfig
  , toNativeConfig
  )
  where

import Prelude

import Data.Maybe (maybe)
import Data.Nullable (Nullable, toMaybe)
import Data.Time.Duration (Milliseconds(..))
import Prim.Row (class Union)
import Record.Unsafe (unsafeGet, unsafeSet)
import Unsafe.Coerce (unsafeCoerce)


data RoughAnnotationType = Underline | Box | Circle | Highlight | StrikeThrough | CrossedOff | Bracket
instance Show RoughAnnotationType where
  show = case _ of
    Underline -> "underline"
    Box -> "box"
    Circle -> "circle"
    Highlight -> "highlight"
    StrikeThrough -> "strike-through"
    CrossedOff -> "crossed-off"
    Bracket -> "bracket"

data RoughPadding
  = Padding Number
  -- | SimplePadding [number, number] 
  | FullPadding Number Number Number Number 
paddingAsArray :: RoughPadding -> Array Number
paddingAsArray = case _ of
  Padding padding -> [padding]
  FullPadding left right bottom top -> [left, right, bottom, top]


data BracketType = Left | Right | Top | Bottom
instance Show BracketType where
  show = case _ of
    Left -> "left"
    Right -> "right"
    Top -> "top"
    Bottom -> "bottom"

type ConfigRows =
  ( animate :: Boolean
  , animationDuration :: Milliseconds
  , color :: String
  , strokeWidth :: Number
  , padding :: RoughPadding --
  , iterations :: Int
  , brackets :: Array BracketType --
  , multiline :: Boolean
  , rtl :: Boolean
  )

type Config = Record ConfigRows

defaultConfig ::  Config
defaultConfig =
  { animate: true
  , animationDuration: Milliseconds 800.0
  , color: "black"
  , strokeWidth: 2.0
  , padding: Padding 5.0
  , iterations: 2
  , brackets: [Right]
  , multiline: false
  , rtl: false
  }

-- | for type safety reasons, the config that this purescript library uses is slightly different to the rough-notation expects. The type of config that rough-notation requires is called "NativeConfig"

type NativeConfig = 
  { animate :: Boolean
  , animationDuration :: Milliseconds
  , color :: String
  , strokeWidth :: Number
  , padding :: Array Number
  , iterations :: Int
  , brackets :: Array String
  , multiline :: Boolean
  , rtl :: Boolean
  }

toNativeConfig :: Config -> NativeConfig
toNativeConfig config =
  let (padding :: Nullable RoughPadding) = unsafeGet "padding" config
      (bracketType :: Nullable (Array BracketType)) = unsafeGet "brackets" config
  in
    config
      # maybe unsafeCoerce (unsafeSet "padding" <<< paddingAsArray) (toMaybe padding)
      # maybe unsafeCoerce (unsafeSet "brackets" <<< map show) (toMaybe bracketType)