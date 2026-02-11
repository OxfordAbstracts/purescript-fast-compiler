{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "thermite-dom"
, dependencies = [ "thermite", "react", "react-dom", "web-html" ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
