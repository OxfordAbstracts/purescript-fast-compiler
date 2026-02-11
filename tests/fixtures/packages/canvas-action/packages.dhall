let upstream =
      https://github.com/purescript/package-sets/releases/download/psc-0.15.0-20220503/packages.dhall
        sha256:847d49acea4803c3d42ef46114053561e91840e35ede29f0a8014d09d47cd8df

let overrides = {=}

let additions =
  { polymorphic-vectors =
    { dependencies =
      [ "distributive"
      , "foldable-traversable"
      , "numbers"
      , "prelude"
      , "record"
      , "safe-coerce"
      , "type-equality"
      , "typelevel-prelude"
      ]
    , repo = "https://github.com/artemisSystem/purescript-polymorphic-vectors.git"
    , version = "v4.0.0"
    }
  }

in  upstream // overrides // additions
