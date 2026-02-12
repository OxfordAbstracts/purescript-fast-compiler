# original compiler test fixtures 

These directories contain test fixtures from the original PureScript compiler. They are used in tests that compare the output of the new compiler against the original. They are not intended to be edited.

They should be compiled in groups together with any submodules. For example, `passing/MyModule.purs` should be compiled with `passing/MyModule/SubModule.purs` if it exists.


All modules should have access to Prim, Prelude and all modules in support packages should be available.


The support modules are: 
  arrays
  assert
  bifunctors
  catenable-lists
  console
  const
  contravariant
  control
  datetime
  distributive
  effect
  either
  enums
  exceptions
  exists
  filterable
  foldable-traversable
  foreign
  foreign-object
  free 
  gen 
  graphs
  identity
  integers
  invariant
  json
  lazy
  lcg
  lists
  maybe
  newtype
  ordered-collections
  orders
  partial
  profunctor
  quickcheck
  record
  refs
  safe-coerce
  semirings
  st
  strings
  tailrec
  transformers
  tuples
  type-equality 
  typelevel-prelude 
  unfoldable 
  unsafe-coerce 
  validation






# Passing 

The `passing` directory contains modules that should compile successfully. They may be used in tests that check for successful compilation, or that compare the output of the new compiler against the original on successfully compiling code. 

# Failing 

The `failing` directory contains modules that should fail to compile. They contain a comment at the top of the file indicating the expected error message. 