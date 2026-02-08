module Data.Material.Material where

import Prelude
import Data.Maybe (Maybe(..))

type Material =
  { transparent :: Maybe Boolean
  , opacity :: Maybe Number
  , color :: Maybe Int
  , emissiveColor :: Maybe Int
  , emissiveIntensity :: Maybe Number
  , needsUpdate :: Maybe Boolean
  , visible :: Maybe Boolean
  }

select :: Material
select =
  { transparent: pure true
  , opacity: pure 0.75
  , color: pure 0x40E0D0
  , emissiveColor: pure 0xffffff
  , emissiveIntensity: pure 0.1
  , needsUpdate: pure true
  , visible: Nothing
  }

glow :: Material
glow =
  { transparent: Nothing
  , opacity: Nothing
  , color: Nothing
  , emissiveColor: pure 0xffffff
  , emissiveIntensity: pure 0.05
  , needsUpdate: pure true
  , visible: Nothing
  }

unglow :: Material
unglow =
  { transparent: Nothing
  , opacity: Nothing
  , color: Nothing
  , emissiveColor: Nothing
  , emissiveIntensity: pure 0.0
  , needsUpdate: pure true
  , visible: Nothing
  }

emptyMaterial :: Material
emptyMaterial =
  { transparent: Nothing
  , opacity: Nothing
  , color: Nothing
  , emissiveColor: Nothing
  , emissiveIntensity: Nothing
  , needsUpdate: Nothing
  , visible: Nothing
  }

transparentAs :: Boolean -> Material -> Material
transparentAs transparent materialUpdate = materialUpdate { transparent = pure transparent }

visibleAs :: Boolean -> Material -> Material
visibleAs visible materialUpdate = materialUpdate { visible = pure visible }

alsoHide :: Material -> Material
alsoHide materialUpdate = visibleAs false materialUpdate

hide :: Material
hide = visibleAs false emptyMaterial

unhide :: Material
unhide = visibleAs true emptyMaterial

colorAs :: Int -> Material
colorAs color = emptyMaterial { color = pure color }
