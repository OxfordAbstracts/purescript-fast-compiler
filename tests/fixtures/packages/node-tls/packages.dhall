let upstream =
      https://github.com/purescript/package-sets/releases/download/psc-0.15.8-20230615/packages.dhall
        sha256:96d5db51eb6ce51906b52377d615fcdca3528ac05e0dc58e71ace8bbaceac108

in  upstream
      with node-event-emitter.version = "v3.0.0"
      with node-event-emitter.dependencies =
        [ "effect"
        , "either"
        , "functions"
        , "maybe"
        , "nullable"
        , "prelude"
        , "unsafe-coerce"
        ]
      with node-buffer.version = "v9.0.0"
      with node-buffer.dependencies =
        [ "arraybuffer-types"
        , "effect"
        , "maybe"
        , "st"
        , "unsafe-coerce"
        , "nullable"
        ]
      with node-streams.version = "v9.0.0"
      with node-streams.dependencies =
        [ "aff"
        , "effect"
        , "exceptions"
        , "maybe"
        , "node-buffer"
        , "node-event-emitter"
        , "nullable"
        , "prelude"
        , "unsafe-coerce"
        ]
      with node-fs.version = "v9.1.0"
      with node-fs.dependencies =
        [ "datetime"
        , "effect"
        , "either"
        , "enums"
        , "exceptions"
        , "functions"
        , "integers"
        , "js-date"
        , "maybe"
        , "node-buffer"
        , "node-path"
        , "node-streams"
        , "nullable"
        , "partial"
        , "prelude"
        , "strings"
        , "unsafe-coerce"
        ]
      with node-net.version = "v5.1.0"
      with node-net.dependencies =
        [ "console"
        , "datetime"
        , "effect"
        , "exceptions"
        , "maybe"
        , "node-buffer"
        , "node-event-emitter"
        , "node-fs"
        , "node-streams"
        , "nullable"
        , "partial"
        , "prelude"
        , "unsafe-coerce"
        ]
