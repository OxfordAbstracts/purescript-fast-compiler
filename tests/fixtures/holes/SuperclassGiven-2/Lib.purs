module SuperclassGiven.Lib where

class Super m where
  member :: { key :: String } -> m Int

class Super m <= Cl m
