module Main where

import Prelude
import Effect.Console

-- Simple one-level nested update
type Inner = { x :: Int, y :: Int }
type Outer = { inner :: Inner, name :: String }

outerVal :: Outer
outerVal = { inner: { x: 1, y: 2 }, name: "test" }

updated1 :: Outer
updated1 = outerVal { inner { x = 10 } }

-- Two-level nested update
type Deep = { a :: { b :: { c :: Int, d :: String }, e :: Boolean } }

deepVal :: Deep
deepVal = { a: { b: { c: 1, d: "hello" }, e: true } }

updated2 :: Deep
updated2 = deepVal { a { b { c = 99 } } }

-- Mixed flat and nested updates
updated3 :: Deep
updated3 = deepVal { a { b { c = 42, d = "world" }, e = false } }

-- Nested update on a polymorphic record
updateInner :: forall r. { inner :: { x :: Int | r } | r } -> { inner :: { x :: Int | r } | r }
updateInner rec = rec { inner { x = 0 } }

-- Nested update preserving other fields
type Config = { db :: { host :: String, port :: Int }, debug :: Boolean }

defaultConfig :: Config
defaultConfig = { db: { host: "localhost", port: 5432 }, debug: false }

updatedConfig :: Config
updatedConfig = defaultConfig { db { port = 3306 } }

-- Verify values at runtime
main = do
  when (updated1.inner.x == 10 && updated1.inner.y == 2 && updated1.name == "test") $ log "test1"
  when (updated2.a.b.c == 99 && updated2.a.b.d == "hello" && updated2.a.e == true) $ log "test2"
  when (updated3.a.b.c == 42 && updated3.a.b.d == "world" && updated3.a.e == false) $ log "test3"
  when (updatedConfig.db.port == 3306 && updatedConfig.db.host == "localhost") $ log "test4"
  log "Done"
