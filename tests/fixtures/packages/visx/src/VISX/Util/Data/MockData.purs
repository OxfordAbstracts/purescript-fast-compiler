module VISX.Util.Data.MockData where

type LetterFrequency = { letter :: String, frequency :: Number }

foreign import letterFrequency :: Array LetterFrequency
