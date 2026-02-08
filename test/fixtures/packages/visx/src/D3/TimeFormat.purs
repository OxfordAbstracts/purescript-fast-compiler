module D3.TimeFormat where

import D3.Format (D3Format)
import Unsafe.Coerce (unsafeCoerce)

foreign import data D3TimeFormat ∷ Type

foreign import timeFormat ∷ String → D3TimeFormat

foreign import data D3TimeFormatLocale ∷ Type

foreign import timeFormatLocale ∷ D3TimeFormatLocaleDefinition → D3TimeFormatLocale

newtype D3TimeFormatLocaleDefinition
  = D3TimeFormatLocaleDefinition
  { decimal ∷ String
  , thousands ∷ String
  , grouping ∷ Array Int
  , currency ∷ Array String
  , dateTime ∷ String
  , date ∷ String
  , time ∷ String
  , periods ∷ Array String
  , days ∷ Array String
  , shortDays ∷ Array String
  , months ∷ Array String
  , shortMonths ∷ Array String
  }

foreign import localeTimeFormat ∷ String → D3TimeFormatLocale → D3TimeFormat

toD3Format ∷ D3TimeFormat → D3Format
toD3Format = unsafeCoerce
