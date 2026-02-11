{ name = "my-project"
, dependencies =
  [ "console"
  , "effect"
  , "either"
  , "exceptions"
  , "foreign"
  , "maybe"
  , "node-buffer"
  , "node-event-emitter"
  , "node-net"
  , "nullable"
  , "partial"
  , "prelude"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "MIT"
}
