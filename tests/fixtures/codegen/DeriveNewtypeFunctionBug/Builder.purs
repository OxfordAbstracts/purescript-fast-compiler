module Builder where

import Prelude hiding (identity)
import Data.Function (flip) as Function

-- A newtype wrapping the function arrow, exactly like Record.Builder.
-- `derive newtype instance` on a class whose existing instance is for (->)
-- triggers the bug: our codegen generates `var semigroupoidBuilder = semigroupoidFunction`
-- where `semigroupoidFunction` is undefined, instead of importing and referencing
-- `semigroupoidFn` from Control.Semigroupoid.
newtype Builder a b = Builder (a -> b)

derive newtype instance semigroupoidBuilder :: Semigroupoid Builder
derive newtype instance categoryBuilder :: Category Builder

-- Build by running the builder
build :: forall a b. Builder a b -> a -> b
build (Builder f) = f
