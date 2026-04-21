module AliasModule where

-- Defines a type alias with the SAME unqualified name as the data type
-- in DataModule. This simulates the real-world scenario where
-- `type ProgramType = { name :: String }` collides with `data ProgramType`.
type ProgramType = { name :: String, code :: Int }
