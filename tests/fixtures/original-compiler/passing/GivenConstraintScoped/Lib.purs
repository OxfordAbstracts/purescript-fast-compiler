module GivenConstraintScoped.Lib where

class Super m where
  member :: String -> m String

class Super m <= Cl m
