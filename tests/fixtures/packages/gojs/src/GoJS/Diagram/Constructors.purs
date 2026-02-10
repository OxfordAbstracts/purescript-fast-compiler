module GoJS.Diagram.Constructors where

import Effect (Effect)
import GoJS.Diagram (Diagram_)
import GoJS.Unsafe.Constructor (constructor1)

newDiagram :: String -> Effect Diagram_
newDiagram = constructor1 "Diagram"
