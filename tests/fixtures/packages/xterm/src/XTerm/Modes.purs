module XTerm.Modes where

type Modes =
  { applicationCursorKeysMode :: Boolean
  , applicationKeypadMode :: Boolean
  , bracketedPasteMode :: Boolean
  , insertMode :: Boolean
  , mouseTrackingMode :: String
  , originMode :: Boolean
  , reverseWraparoundMode :: Boolean
  , sendFocusMode :: Boolean
  , wraparoundMode :: Boolean
  }
