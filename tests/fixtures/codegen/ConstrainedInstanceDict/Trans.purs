-- | Defines a Writer-like transformer with a constrained Accum instance.
-- | The key bug: the instance `accumWriterT` has constraints (Combine w, Wrap m)
-- | so its generated JS must be a function taking dict args, not a bare object.
module Trans where

import Classes (class Combine, cempty, cappend, class Wrap, wpure, class Accum, accum)

data Pair a b = Pair a b

-- WriterT-like transformer
newtype WriterT w m a = WriterT (m (Pair a w))

-- THE CRITICAL INSTANCE: has two constraints.
-- Reference compiler generates:
--   var accumWriterT = function(dictCombine) {
--     return function(dictWrap) {
--       return { accum: function(w) { ... } };
--     };
--   };
-- Bug generates:
--   var accumWriterT = { accum: function(w) { ... } };
instance accumWriterT :: (Combine w, Wrap m) => Accum w (WriterT w m) where
  accum w = WriterT (wpure (Pair 0 w))
