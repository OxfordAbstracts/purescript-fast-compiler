module GoJS.Geometry.Margin.Constructors where

import GoJS.Geometry.Types (Margin_)

foreign import newMargin :: forall b l r t. b -> l -> r -> t -> Margin_
