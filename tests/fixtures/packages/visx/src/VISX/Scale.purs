module VISX.Scale
  ( class Scale
  , scaled
  , invert
  , LinearScale
  , scaleLinear
  , TimeScale
  , scaleTime
  , QuantizeScale
  , scaleQuantize
  , OrdinalScale
  , scaleOrdinal
  , BandScale
  , scaleBand
  , bandwidth
  ) where

import Prelude
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.JSDate (JSDate)
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Foreign (Foreign)
import Prim.Row (class Lacks)
import Record.Builder as Builder
import Type.Proxy (Proxy(..))
import VISX.FFI (class Options, class WriteForeign, toOptions)
import VISX.FFI as FFI

class Scale ∷ ∀ k. k → Constraint
class Scale scale

foreign import scaleValueImpl ∷ ∀ scale domain range. scale → domain → range

scaled ∷
  ∀ scale domain range.
  Scale (scale domain range) ⇒
  domain → scale domain range → range
scaled = flip scaleValueImpl

foreign import invertValueImpl ∷ ∀ scale domain range. scale → range → domain

invert ∷
  ∀ scale domain range.
  Scale (scale domain range) ⇒
  range →
  scale domain range →
  domain
invert = flip invertValueImpl

-- Linear Scale
foreign import data LinearScale ∷ Type → Type → Type
instance Scale (LinearScale a b)

type LinearScaleConfig
  = { domain ∷ Number /\ Number
    , range ∷ Number /\ Number
    , round ∷ Maybe Boolean
    , nice ∷ Maybe Boolean
    , clamp ∷ Maybe Boolean
    }

foreign import scaleLinearImpl ∷ ∀ a. Foreign → LinearScale Number a

scaleLinear ∷
  ∀ opt.
  Options opt LinearScaleConfig ⇒
  opt →
  LinearScale Number _
scaleLinear config =
  scaleLinearImpl
    (FFI.write (toOptions config ∷ LinearScaleConfig))

-- Time Scale
foreign import data TimeScale ∷ Type → Type → Type
instance Scale (TimeScale a b)

type TimeScaleConfig
  = { domain ∷ JSDate /\ JSDate
    , range ∷ Number /\ Number
    , round ∷ Maybe Boolean
    , nice ∷ Maybe Boolean
    , clamp ∷ Maybe Boolean
    }

foreign import scaleTimeImpl ∷ ∀ a. Foreign → TimeScale JSDate a

scaleTime ∷
  ∀ opt.
  Options opt TimeScaleConfig ⇒
  opt →
  TimeScale JSDate _
scaleTime config =
  scaleTimeImpl
    (FFI.write (toOptions config ∷ TimeScaleConfig))

-- Band Scale
foreign import data BandScale ∷ Type → Type → Type
instance Scale (BandScale a b)

type BandScaleConfig a
  = { domain ∷ Array a
    , range ∷ Number /\ Number
    , round ∷ Maybe Boolean
    , padding ∷ Maybe Number
    }

foreign import scaleBandImpl ∷ ∀ a b. Foreign → (BandScale a b)

scaleBand ∷
  ∀ opt a b.
  Options opt (BandScaleConfig a) ⇒
  WriteForeign a ⇒
  opt →
  BandScale a b
scaleBand config =
  scaleBandImpl
    (FFI.write (toOptions config ∷ (BandScaleConfig a)))

foreign import bandwidth ∷ ∀ a b. BandScale a b → Effect b

-- Quantised Scale
foreign import data QuantizeScale ∷ Type → Type → Type
instance Scale (QuantizeScale a b)

type QuantizeScaleConfig a
  = { domain ∷ Int /\ Int
    , range ∷ Array a
    }

foreign import scaleQuantizeImpl ∷ ∀ a b. Foreign → (QuantizeScale a b)

scaleQuantize ∷
  ∀ opt a b.
  Options opt (QuantizeScaleConfig a) ⇒
  WriteForeign a ⇒
  opt →
  QuantizeScale a b
scaleQuantize config =
  scaleQuantizeImpl
    (FFI.write (toOptions config ∷ (QuantizeScaleConfig a)))

-- Ordinal Scale
foreign import data OrdinalScale ∷ Type → Type → Type
instance Scale (OrdinalScale domain codomain)

type OrdinalScaleConfig domain codomain
  = { domainAndRange ∷ NonEmptyArray (Tuple domain codomain)
    }

type OrdinalScaleConfigImpl domain codomain
  = { domain ∷ NonEmptyArray domain
    , range ∷ NonEmptyArray codomain
    }

foreign import scaleOrdinalImpl ∷
  ∀ domain codomain.
  Foreign →
  (OrdinalScale domain codomain)

scaleOrdinal ∷
  ∀ opt domain codomain.
  Options { domain ∷ NonEmptyArray domain, range ∷ NonEmptyArray codomain | opt } (OrdinalScaleConfigImpl domain codomain) ⇒
  WriteForeign domain ⇒
  WriteForeign codomain ⇒
  Lacks "domain" opt ⇒
  Lacks "range" opt ⇒
  Lacks "domainAndRange" opt ⇒
  { domainAndRange ∷ NonEmptyArray (domain /\ codomain) | opt } →
  OrdinalScale domain codomain
scaleOrdinal config =
  scaleOrdinalImpl (FFI.write configImpl)
  where
  domain /\ range = NEA.unzip config.domainAndRange
  configImpl ∷ OrdinalScaleConfigImpl domain codomain
  configImpl =
    toOptions
      $ ( ( Builder.build
              ( Builder.delete (Proxy ∷ Proxy "domainAndRange")
                  >>> Builder.insert (Proxy ∷ Proxy "domain") domain
                  >>> Builder.insert (Proxy ∷ Proxy "range") range
              )
              config
          ) ∷
            { domain ∷ NonEmptyArray domain, range ∷ NonEmptyArray codomain | opt }
        )
