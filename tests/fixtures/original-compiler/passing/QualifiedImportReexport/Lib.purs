module QualifiedImportReexport.Lib where

-- Both foo and bar are exported. When this module is re-exported via
-- `module QualifiedImportReexport.Lib` in the main module, only names
-- from the *explicit* import should be included, not those from the
-- qualified-only import.
foo :: Int -> Int
foo x = x

bar :: Int -> Int
bar x = x
