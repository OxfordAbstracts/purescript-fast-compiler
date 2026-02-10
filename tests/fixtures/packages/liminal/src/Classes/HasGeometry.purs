module Classes.HasGeometry where

class HasGeometry m g | m -> g where
  getGeometry :: m -> g