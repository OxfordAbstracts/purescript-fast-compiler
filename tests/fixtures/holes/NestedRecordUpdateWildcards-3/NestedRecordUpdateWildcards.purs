module Main where

import Prelude
import Effect.Console

update = _ { foo = _, bar { baz = _, qux = _ } }

init = { foo: 1, bar: { baz: 2, qux: 3 } }

after = ?test

expected = { foo: 10, bar: { baz: 20, qux: 30 } }

check l r =
  l.foo == r.foo &&
  l.bar.baz == r.bar.baz &&
  l.bar.qux == r.bar.qux

main = do
  when (check after expected) $ log "Done"
