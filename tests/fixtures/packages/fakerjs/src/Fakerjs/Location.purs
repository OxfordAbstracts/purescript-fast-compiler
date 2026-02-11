module Fakerjs.Location where

import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Fakerjs.Core.Types (Faker)
import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Fakerjs.Data.Undefinable (Undefinable)
import Fakerjs.Data.Undefinable as Undefinable
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Exception (throw)

-- | Foreign function interface helpers
foreign import zipCodeImpl :: EffectFn2 Faker { state :: Undefinable String, format :: Undefinable String } String
foreign import cityImpl :: EffectFn1 Faker String
foreign import buildingNumberImpl :: EffectFn1 Faker String
foreign import streetImpl :: EffectFn1 Faker String
foreign import streetAddressImpl :: EffectFn2 Faker { useFullAddress :: Boolean } String
foreign import secondaryAddressImpl :: EffectFn1 Faker String
foreign import countyImpl :: EffectFn1 Faker String
foreign import countryImpl :: EffectFn1 Faker String
foreign import continentImpl :: EffectFn1 Faker String
foreign import countryCodeImpl :: EffectFn2 Faker String String
foreign import stateImpl :: EffectFn2 Faker { abbreviated :: Boolean } String
foreign import latitudeImpl :: EffectFn2 Faker { max :: Number, min :: Number, precision :: Int } Number
foreign import longitudeImpl :: EffectFn2 Faker { max :: Number, min :: Number, precision :: Int } Number
foreign import directionImpl :: EffectFn2 Faker { abbreviated :: Boolean } String
foreign import cardinalDirectionImpl :: EffectFn2 Faker { abbreviated :: Boolean } String
foreign import ordinalDirectionImpl :: EffectFn2 Faker { abbreviated :: Boolean } String
foreign import nearbyGPSCoordinateImpl :: EffectFn2 Faker { origin :: Undefinable (Array Number), radius :: Number, isMetric :: Boolean } (Array Number)
foreign import timeZoneImpl :: EffectFn1 Faker String
foreign import languageImpl :: EffectFn1 Faker Language

--------------------------------------------------------------

-- | Generates random zip code from specified format
zipCode :: Faker -> { state :: Maybe String, format :: Maybe String } -> Effect String
zipCode faker o = runEffectFn2 zipCodeImpl faker { state: Undefinable.toUndefinable o.state, format: Undefinable.toUndefinable o.format }

zipCode_ :: Faker -> Effect String
zipCode_ faker = zipCode faker { state: Nothing, format: Nothing }

--------------------------------------------------------------

-- | Generates a random localized city name
city :: Faker -> Effect String
city = runEffectFn1 cityImpl

-- | Generates a random building number
buildingNumber :: Faker -> Effect String
buildingNumber = runEffectFn1 buildingNumberImpl

-- | Generates a random localized street name
street :: Faker -> Effect String
street = runEffectFn1 streetImpl

---------------------------------

streetAddress :: Faker -> { useFullAddress :: Boolean } -> Effect String
streetAddress = runEffectFn2 streetAddressImpl

streetAddress_ :: Faker -> Effect String
streetAddress_ faker = streetAddress faker { useFullAddress: false }

---------------------------------

-- | Generates a random localized secondary address
secondaryAddress :: Faker -> Effect String
secondaryAddress = runEffectFn1 secondaryAddressImpl

-- | Returns a random localized county
county :: Faker -> Effect String
county = runEffectFn1 countyImpl

-- | Returns a random country name
country :: Faker -> Effect String
country = runEffectFn1 countryImpl

-- | Returns a random continent name
continent :: Faker -> Effect String
continent = runEffectFn1 continentImpl

-----------------------------------
-- | Type for country code variant
data CountryCodeVariant = Alpha2 | Alpha3 | Numeric

derive instance Generic CountryCodeVariant _
derive instance Eq CountryCodeVariant
derive instance Ord CountryCodeVariant
instance Show CountryCodeVariant where
  show = genericShow

countryCodeVariantToInternalString :: CountryCodeVariant -> String
countryCodeVariantToInternalString Alpha2 = "alpha-2" -- default
countryCodeVariantToInternalString Alpha3 = "alpha-3"
countryCodeVariantToInternalString Numeric = "numeric"

-- | Returns a random ISO_3166-1 country code
countryCode :: Faker -> CountryCodeVariant -> Effect String
countryCode faker variant = runEffectFn2 countryCodeImpl faker (countryCodeVariantToInternalString variant)

countryCode_ :: Faker -> Effect String
countryCode_ faker = countryCode faker Alpha2

-----------------------------------

-- | Returns a random localized state
state :: Faker -> { abbreviated :: Boolean } -> Effect String
state = runEffectFn2 stateImpl

state_ :: Faker -> Effect String
state_ faker = state faker { abbreviated: false }

-----------------------------------

-- | Generates a random latitude
latitude :: Faker -> { max :: Number, min :: Number, precision :: Int } -> Effect Number
latitude = runEffectFn2 latitudeImpl

latitude_ :: Faker -> Effect Number
latitude_ faker = latitude faker { max: 90.0, min: -90.0, precision: 4 }

-----------------------------------

longitude :: Faker -> { max :: Number, min :: Number, precision :: Int } -> Effect Number
longitude = runEffectFn2 longitudeImpl

longitude_ :: Faker -> Effect Number
longitude_ faker = longitude faker { max: 180.0, min: -180.0, precision: 4 }

-----------------------------------
-- | Returns a random direction
direction :: Faker -> { abbreviated :: Boolean } -> Effect String
direction = runEffectFn2 directionImpl

direction_ :: Faker -> Effect String
direction_ faker = direction faker { abbreviated: false }

-- | Returns a random cardinal direction
cardinalDirection :: Faker -> { abbreviated :: Boolean } -> Effect String
cardinalDirection = runEffectFn2 cardinalDirectionImpl

cardinalDirection_ :: Faker -> Effect String
cardinalDirection_ faker = cardinalDirection faker { abbreviated: false }

-- | Returns a random ordinal direction
ordinalDirection :: Faker -> { abbreviated :: Boolean } -> Effect String
ordinalDirection = runEffectFn2 ordinalDirectionImpl

ordinalDirection_ :: Faker -> Effect String
ordinalDirection_ faker = ordinalDirection faker { abbreviated: false }

-----------------------------------

type Coordinate = { latitude :: Number, longitude :: Number }

type NearbyGPSCoordinateOptions = { origin :: Maybe Coordinate, radius :: Number, isMetric :: Boolean }

-- | Generates a random GPS coordinate within the specified radius from the given coordinate
nearbyGPSCoordinate :: Faker -> NearbyGPSCoordinateOptions -> Effect Coordinate
nearbyGPSCoordinate faker { origin, radius, isMetric } =
  runEffectFn2 nearbyGPSCoordinateImpl faker { origin: Undefinable.toUndefinable (map (\c -> [ c.latitude, c.longitude ]) origin), radius, isMetric } >>=
    case _ of
      [ la, lo ] -> pure { latitude: la, longitude: lo }
      _ -> throw "nearbyGPSCoordinate: wrong output"

nearbyGPSCoordinate_ :: Faker -> Effect Coordinate
nearbyGPSCoordinate_ faker = nearbyGPSCoordinate faker { origin: Nothing, radius: 10.0, isMetric: false }

-----------------------------------
-- | Returns a random IANA time zone relevant to this locale
timeZone :: Faker -> Effect String
timeZone = runEffectFn1 timeZoneImpl

-----------------------------------

-- | Represents a language with its full name, 2 character ISO 639-1 code, and 3 character ISO 639-2 code.
type Language = { name :: String, alpha2 :: String, alpha3 :: String }

-- | Returns a random spoken language
language :: Faker -> Effect Language
language = runEffectFn1 languageImpl
