module VISX.Annotation where

import Prelude
import React.Basic (ReactComponent)

foreign import annotationImpl ∷ ∀ a. ReactComponent { | a }

foreign import editableAnnotationImpl ∷ ∀ a. ReactComponent { | a }

foreign import circleSubjectImpl ∷ ∀ a. ReactComponent { | a }

foreign import connectorImpl ∷ ∀ a. ReactComponent { | a }

foreign import annotationContextImpl ∷ ∀ a. ReactComponent { | a }

foreign import labelImpl ∷ ∀ a. ReactComponent { | a }

foreign import linePathAnnotationImpl ∷ ∀ a. ReactComponent { | a }

foreign import lineSubjectImpl ∷ ∀ a. ReactComponent { | a }
