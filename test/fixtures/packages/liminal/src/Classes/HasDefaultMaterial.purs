module Classes.HasDefaultMaterial where

import Data.Material.Material (Material)

class HasDefaultMaterial m where
  getDefaultMaterial :: m -> Material
