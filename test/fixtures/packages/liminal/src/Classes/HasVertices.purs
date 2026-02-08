module Classes.HasVertices where

import Prelude
import Data.TransformationMatrix.Vector3 (Vector3)
import Data.TransformationMatrix.Matrix4 (Matrix4, setPosition)
import Classes.HasMatrix (class HasMatrix, getMatrix)

class HasVertices m t | m -> t where
  getVertices :: m -> t (Vector3 Number)

getMatricesAtVertices
  :: forall a f
   . HasMatrix a
  => HasVertices a f
  => Functor f
  => a
  -> f Matrix4
getMatricesAtVertices object = (flip setPosition matrix) <$> vertices
  where
  matrix = getMatrix object
  vertices = getVertices object
