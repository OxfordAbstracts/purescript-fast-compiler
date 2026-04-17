module Test.Multi.AsB where

-- `import Test.Multi.AsA as Q` — bare `answer` must not
-- resolve; `Q.answer` must.
import Test.Multi.AsA as Q

twice :: Int
twice = Q.answer
