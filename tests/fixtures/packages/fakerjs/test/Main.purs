module Test.Main where

import Prelude
import Prelude

import Data.Array.NonEmpty as NonEmptyArray
import Data.List.Lazy as List
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect (Effect)
import Effect.Console (log)
import Effect.Random (randomInt)
import Fakerjs (makeFaker, base, en)
import Fakerjs.Location as Location

main :: Effect Unit
main = do
  let faker = makeFaker (NonEmptyArray.cons' base [ en ]) (Just 1)

  -- Basic location examples
  Location.city faker >>= (\c -> log $ "City: " <> c)

  Location.street faker >>= \s -> log $ "Street: " <> s
  Location.country faker >>= \c -> log $ "Country: " <> c
  Location.continent faker >>= \c -> log $ "Continent: " <> c
  Location.buildingNumber faker >>= \n -> log $ "Building Number: " <> n
  Location.timeZone faker >>= \tz -> log $ "Time Zone: " <> tz

  -- Using options
  Location.zipCode_ faker >>= \z -> log $ "Zip Code: " <> z
  Location.streetAddress_ faker >>= \sa -> log $ "Street Address: " <> sa

  -- State with options
  Location.state_ faker >>= \s -> log $ "State: " <> s
  Location.state faker { abbreviated: true } >>= \s -> log $ "State Abbreviated: " <> s

  -- Country code
  Location.countryCode faker Location.Alpha2 >>= \cc -> log $ "Country Code (Alpha-2): " <> cc
  Location.countryCode faker Location.Alpha3 >>= \cc -> log $ "Country Code (Alpha-3): " <> cc
  Location.countryCode faker Location.Numeric >>= \cc -> log $ "Country Code (Numeric): " <> cc

  -- Directions
  Location.direction faker { abbreviated: false } >>= \d -> log $ "Direction: " <> d
  Location.direction faker { abbreviated: true } >>= \d -> log $ "Direction Abbreviated: " <> d
  Location.cardinalDirection faker { abbreviated: false } >>= \cd -> log $ "Cardinal Direction: " <> cd
  Location.ordinalDirection faker { abbreviated: false } >>= \od -> log $ "Ordinal Direction: " <> od

  -- Coordinates
  Location.latitude faker { max: 90.0, min: -90.0, precision: 4 } >>= \lat ->
    Location.longitude faker { max: 180.0, min: -180.0, precision: 4 } >>= \lng -> do
      log $ "Latitude: " <> show lat
      log $ "Longitude: " <> show lng

      -- Nearby GPS coordinates
      Location.nearbyGPSCoordinate faker { origin: Just { latitude: lat, longitude: lng }, radius: 10.0, isMetric: false } >>= \coords ->
        log $ "Nearby GPS Coordinates: " <> show coords

  -- Language
  Location.language faker >>= \lang ->
    log $ "Language: " <> lang.name <> " (" <> lang.alpha2 <> ", " <> lang.alpha3 <> ")"
