module DataModule where

-- Defines a data type `ProgramType`
data ProgramType = Talk | Poster | Workshop

showPT :: ProgramType -> String
showPT Talk = "talk"
showPT Poster = "poster"
showPT Workshop = "workshop"
