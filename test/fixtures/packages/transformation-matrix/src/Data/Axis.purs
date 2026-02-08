module Data.TransformationMatrix.Axis where

newtype X = X Number
newtype Y = Y Number
newtype Z = Z Number

data Axis = Xaxis Y Z | Yaxis X Z | Zaxis X Y
