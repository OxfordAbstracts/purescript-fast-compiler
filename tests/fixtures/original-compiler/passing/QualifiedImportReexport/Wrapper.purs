module QualifiedImportReexport.Wrapper where

-- Defines its own `foo`, different from Lib.foo
foo :: String -> String
foo _ = "wrapped"
