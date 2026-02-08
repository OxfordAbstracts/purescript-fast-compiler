module Data.Geometria 
  ( module Data.Geometria.Types
  , module Data.Geometria.Ellipse
  , module Data.Geometria.Space
  ) where

import Data.Geometria.Types 
  ( class Analytic
  , class EuclideanSpace
  , class Intersectable
  , class Metric
  , class Shape
  , Circle(..), HalfLine(..), Line(..), Point(..), Segment(..), Vector(..), System
  , circle, halfline, line, point, segment, vector
  , anyPoint, anyVector
  , cosAngle, dot, freeVector, fromCoordinates
  , index, length, meets, middle, normalTo, normalized
  , projection, rotated, scale, shape, system, toCoordinates, translatedBy
  , immerse, drain, projector, project
  , (<+|)
  )

import Data.Geometria.Ellipse 
  ( Ellipse(..)
  , cardinal, ellipse, ellipseCenter, ellipseDimensions, ellipseInternal
  , foci, fromUnitCircle, residualConstant
  , rytz, steiner, unCouple
  , quadratic, brianchon, turnEllipse, moveEllipse, expandEllipse
  , mkMatrix
  )

import Data.Geometria.Space
  ( landing
  , land
  , revolution
  )
