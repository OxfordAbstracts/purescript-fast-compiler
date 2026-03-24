module ForeignImport where

foreign import log :: String -> String
foreign import pi :: Number

test = log "hello"

-- TEST: "hello"
